module

public import CFSG.Quasithin.EmptyFaithful.QTKELocal
public import CFSG.Quasithin.Background.A1cA131
public import CFSG.Quasithin.Background.B2FactorizationBridge
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.Background.A4Defs

public section

open CFSG.QuasithinUnique (quasithinIsQTKECat)

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits

theorem centralizer_le_of_normal_odd151b {Q : Type*} [Group Q] [Finite Q] (P : Subgroup Q)
    [P.Normal] (hQ : ∀ x : Q, ∃ k : ℕ, x ^ (2 ^ k) ∈ P)
    (hO2 : ∀ N : Subgroup Q, N.Normal → IsPGroup 2 N → N = ⊥) :
    Subgroup.centralizer (P : Set Q) ≤ P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := Subgroup.centralizer (P : Set Q) with hC
  have hCn : C.Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_centralizer_iff] at hn ⊢
    intro p hp
    have hp' : g⁻¹ * p * g ∈ P := by
      have := (inferInstance : P.Normal).conj_mem p hp g⁻¹
      simpa using this
    have h1 := hn _ hp'
    calc p * (g * n * g⁻¹) = g * ((g⁻¹ * p * g) * n) * g⁻¹ := by group
      _ = g * (n * (g⁻¹ * p * g)) * g⁻¹ := by rw [h1]
      _ = g * n * g⁻¹ * p := by group
  let ZC : Subgroup C := P.subgroupOf C
  have hZc : ZC ≤ Subgroup.center C := by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro y
    have := Subgroup.mem_centralizer_iff.mp y.2 x.1 hx
    exact Subtype.ext this.symm
  have : ZC.Normal := inferInstance
  let f : ↥C →* ↥C ⧸ ZC := QuotientGroup.mk' ZC
  have hker : f.ker ≤ Subgroup.center C := by
    rw [QuotientGroup.ker_mk']
    exact hZc
  have hp2 : IsPGroup 2 (↥C ⧸ ZC) := by
    intro g
    obtain ⟨c, rfl⟩ := QuotientGroup.mk_surjective g
    obtain ⟨k, hk⟩ := hQ (c : Q)
    refine ⟨k, ?_⟩
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact hk
  have : Group.IsNilpotent (↥C ⧸ ZC) := hp2.isNilpotent
  have : Group.IsNilpotent ↥C := Subgroup.isNilpotent_of_ker_le_center f hker
  obtain ⟨S⟩ : Nonempty (Sylow 2 ↥C) := inferInstance
  have hSn : (S : Subgroup ↥C).Normal := inferInstance
  have hSc : (S : Subgroup ↥C).Characteristic := Sylow.characteristic_of_normal S hSn
  set S' : Subgroup Q := (S : Subgroup ↥C).map C.subtype with hS'
  have hS'p : IsPGroup 2 S' := by
    intro z
    obtain ⟨s, hs, hz⟩ := z.2
    obtain ⟨k, hk⟩ := S.isPGroup' ⟨s, hs⟩
    refine ⟨k, Subtype.ext ?_⟩
    have h1 : s ^ 2 ^ k = 1 := congrArg Subtype.val hk
    calc ((z ^ 2 ^ k : S') : Q) = (z : Q) ^ 2 ^ k := rfl
      _ = (C.subtype s) ^ 2 ^ k := by rw [hz]
      _ = 1 := by rw [← map_pow, h1, map_one]
  have hS'n : S'.Normal := by
    refine ⟨fun n hn g => ?_⟩
    obtain ⟨s, hs, rfl⟩ := hn
    have hmap := (Subgroup.characteristic_iff_map_eq.mp hSc) (MulAut.conjNormal (H := C) g)
    have : (MulAut.conjNormal (H := C) g) s ∈ (S : Subgroup ↥C) := by
      rw [← hmap]
      exact ⟨s, hs, rfl⟩
    exact ⟨_, this, by simp [MulAut.conjNormal_apply]⟩
  have hbot : S' = ⊥ := hO2 S' hS'n hS'p
  have hSbot : (S : Subgroup ↥C) = ⊥ := by
    have : (S : Subgroup ↥C).map C.subtype = ⊥ := hbot
    exact (Subgroup.map_eq_bot_iff_of_injective _ C.subtype_injective).mp this
  have hodd : ¬ 2 ∣ Nat.card C := by
    intro h2
    have hcard := Sylow.card_eq_multiplicity S
    rw [hSbot, Subgroup.card_bot] at hcard
    have hpos : 0 < (Nat.card C).factorization 2 :=
      Nat.Prime.factorization_pos_of_dvd Nat.prime_two Nat.card_pos.ne' h2
    have : 2 ^ 1 ≤ 2 ^ (Nat.card C).factorization 2 := Nat.pow_le_pow_right (by norm_num) hpos
    omega
  have hidx : ZC.index = 1 := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hp2
    have hdvd : Nat.card (↥C ⧸ ZC) ∣ Nat.card C := Subgroup.card_quotient_dvd_card ZC
    rw [Subgroup.index_eq_card, hn]
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · rw [h0]; rfl
    · exfalso
      rw [hn] at hdvd
      exact hodd ((dvd_pow_self 2 h0.ne').trans hdvd)
  have htop : ZC = ⊤ := Subgroup.index_eq_one.mp hidx
  intro c hc
  have : (⟨c, hc⟩ : ↥C) ∈ ZC := by rw [htop]; exact Subgroup.mem_top _
  exact this

section Seven

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
noncomputable def autISurj151b {V : Subgroup G} (hV : IsElemAbelian 2 V) (M : Subgroup G)
    (hMN : M ≤ Subgroup.normalizer (V : Set G)) : ↥M →* ↥(autI hV M) :=
  (convHom hV M hMN).codRestrict (autI hV M) (fun x => by
    rw [← range_convHom hV M hMN]
    exact MonoidHom.mem_range.mpr ⟨x, rfl⟩)

omit [Finite G] in
theorem autISurj151b_surjective {V : Subgroup G} (hV : IsElemAbelian 2 V) (M : Subgroup G)
    (hMN : M ≤ Subgroup.normalizer (V : Set G)) : Function.Surjective (autISurj151b hV M hMN) := by
  intro y
  have hy : (y : MulAut (IntMod V hV)) ∈ (convHom hV M hMN).range := by
    rw [range_convHom]
    exact y.2
  obtain ⟨x, hx⟩ := MonoidHom.mem_range.mp hy
  exact ⟨x, Subtype.ext hx⟩

theorem card_le_four_of_threeGroup151b (hK : quasithinIsQTKECat G) {M V : Subgroup G}
    (hM2 : pCoreOf 2 M ≠ ⊥) (hV : IsElemAbelian 2 V) (hMN : M ≤ Subgroup.normalizer (V : Set G))
    (hO2 : pCoreOf 2 (autI hV M) = ⊥) (hP : ∀ x : ↥(oTwoUpper (autI hV M)), x ^ 3 = 1)
    {E : Subgroup (MulAut (IntMod V hV))} (hEX : E ≤ autI hV M) (hE : IsElemAbelian2 E) :
    Nat.card E ≤ 4 := by
  have h2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h3 : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  set X := autI hV M with hX
  have hNX : X ≤ Subgroup.normalizer (oTwoUpper X : Set (MulAut (IntMod V hV))) :=
    le_normalizer_oTwoUpper X
  have hPn : ((oTwoUpper X).subgroupOf X).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hNX
  have hP3 : IsPGroup 3 ((oTwoUpper X).subgroupOf X) := by
    intro x
    refine ⟨1, ?_⟩
    have := hP ⟨x.1.1, Subgroup.mem_subgroupOf.mp x.2⟩
    apply Subtype.ext
    apply Subtype.ext
    simpa using congrArg Subtype.val this
  have hQ : ∀ x : ↥X, ∃ k : ℕ, x ^ (2 ^ k) ∈ (oTwoUpper X).subgroupOf X := by
    intro x
    obtain ⟨k, hk⟩ := exists_pow_mem_oTwoUpper X x.2
    exact ⟨k, Subgroup.mem_subgroupOf.mpr hk⟩
  have hO2' : ∀ N : Subgroup ↥X, N.Normal → IsPGroup 2 N → N = ⊥ := by
    intro N hN hNp
    have hle : N ≤ CFSG.Open.pCore 2 ↥X := le_pCore 2 hN hNp
    have hbot : CFSG.Open.pCore 2 ↥X = ⊥ :=
      (Subgroup.map_eq_bot_iff_of_injective _ X.subtype_injective).mp hO2
    exact le_bot_iff.mp (hbot ▸ hle)
  have hCP : Subgroup.centralizer (((oTwoUpper X).subgroupOf X : Subgroup ↥X) : Set ↥X) ≤
      (oTwoUpper X).subgroupOf X := centralizer_le_of_normal_odd151b _ hQ hO2'
  have hF : Subgroup.centralizer (CFSG.Open.pCore 3 ↥X : Set ↥X) ≤ CFSG.Open.pCore 3 ↥X := by
    have hPle : (oTwoUpper X).subgroupOf X ≤ CFSG.Open.pCore 3 ↥X := le_pCore 3 hPn hP3
    exact (Subgroup.centralizer_le hPle).trans (hCP.trans hPle)
  have hrk3 : CFSG.Open.pRank 3 (⊤ : Subgroup ↥M) ≤ 2 := by
    rw [pRank_top_subtype (p := 3) M]
    exact pRank_le_two_of_pCoreOf_ne_bot hK hM2 (by norm_num) (by norm_num)
  have hconcl := A1c.A131Concl_of_surjective (by norm_num : 3 ≠ 2) hF _ ↥M
    (autISurj151b hV M hMN) (autISurj151b_surjective hV M hMN) rfl hrk3
  have hrk2 : CFSG.Open.pRank 2 (⊤ : Subgroup ↥X) ≤ 2 := hconcl.2.1
  have hE' : IsElemAbelian 2 (E.subgroupOf X) := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun a ha => ?_⟩
    · apply Subtype.ext
      apply Subtype.ext
      exact hE.1 _ a.2 _ b.2
    · have ha' : (a : MulAut (IntMod V hV)) ∈ E := Subgroup.mem_subgroupOf.mp ha
      exact Subtype.ext (by simpa using hE.2 _ ha')
  have hEp : IsPGroup 2 (E.subgroupOf X) := fun x => ⟨1, Subtype.ext (by simpa using hE'.2 x x.2)⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hEp
  have hkle : k ≤ 2 := (le_pRank Nat.prime_two le_top hE' hk).trans hrk2
  have hcardE : Nat.card (E.subgroupOf X) = Nat.card E :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEX).toEquiv
  rw [← hcardE, hk]
  calc 2 ^ k ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hkle
    _ = 4 := by norm_num

end Seven

end CFSG.Quasithin
