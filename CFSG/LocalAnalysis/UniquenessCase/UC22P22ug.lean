module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P22ul
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22ue

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem uc22p22u_sylow_barPreimage {M : Subgroup G} {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    {D : Subgroup (Bar2 M)} (hD : IsPGroup r ↥D) {P : Subgroup G}
    (hP : CFSG.ABGLocalTools.IsSylowOf r P (barPreimage M D)) :
    barImage M P = D ∧ P ⊓ pCoreOf 2 M = ⊥ := by
  haveI : Fact r.Prime := ⟨hr⟩
  set Y : Subgroup G := barPreimage M D with hY
  have hYM : Y ≤ M := uc22p21c_barPreimage_le M D
  obtain ⟨S, hSP⟩ := hP
  have hPsyl : CFSG.ABGLocalTools.IsSylowOf r P Y := ⟨S, hSP⟩
  refine ⟨?_, disjoint_iff.1 (IsPGroup.disjoint_of_ne r 2 hr2 P (pCoreOf 2 M) hPsyl.isPGroup
      (uc22p21c_isPGroup_pCoreOf M))⟩
  apply le_antisymm
  · intro q hq
    obtain ⟨m, hm, rfl⟩ := uc22p21c_mem_barImage.1 hq
    obtain ⟨_, hmD⟩ := uc22p21c_mem_barPreimage.1 (hPsyl.le hm)
    exact hmD
  · let f : ↥Y →* ↥D := ((uc22p21cPi M).comp (Subgroup.inclusion hYM)).codRestrict D fun y => by
      obtain ⟨_, hyD⟩ := uc22p21c_mem_barPreimage.1 y.2
      exact hyD
    have hf : Function.Surjective f := by
      rintro ⟨d, hd⟩
      obtain ⟨m, rfl⟩ := uc22p21c_pi_surjective M d
      exact ⟨⟨(m : G), uc22p21c_mem_barPreimage.2 ⟨m.2, hd⟩⟩, rfl⟩
    have htop : ((S.mapSurjective hf : Sylow r ↥D) : Subgroup ↥D) = ⊤ := by
      symm
      exact (S.mapSurjective hf).is_maximal' (hD.of_equiv Subgroup.topEquiv.symm) le_top
    intro q hq
    have h1 : (⟨q, hq⟩ : ↥D) ∈ ((S.mapSurjective hf : Sylow r ↥D) : Subgroup ↥D) := by
      rw [htop]
      trivial
    rw [Sylow.coe_mapSurjective] at h1
    obtain ⟨s, hs, hsq⟩ := h1
    exact uc22p21c_mem_barImage.2 ⟨Subgroup.inclusion hYM s, hSP ▸ ⟨s, hs, rfl⟩,
      congrArg Subtype.val hsq⟩

theorem uc22p22u_sylow_O2p {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {M P : Subgroup G}
    (hP : CFSG.ABGLocalTools.IsSylowOf p P (F11.O2p p M)) :
    P ≤ M ∧ barImage M P = CFSG.pCore p (Bar2 M) ∧ P ⊓ pCoreOf 2 M = ⊥ := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hP' : CFSG.ABGLocalTools.IsSylowOf p P (barPreimage M (CFSG.pCore p (Bar2 M))) := hP
  obtain ⟨h1, h2⟩ := uc22p22u_sylow_barPreimage hp hp2 (CFSG.pCore_isPGroup (p := p)) hP'
  exact ⟨hP'.le.trans (uc22p21c_barPreimage_le M _), h1, h2⟩

theorem uc22p22u_mem_commutator_iff {M : Subgroup G} (m : ↥M) :
    (m : G) ∈ ⁅M, M⁆ ↔ m ∈ ⁅(⊤ : Subgroup ↥M), (⊤ : Subgroup ↥M)⁆ := by
  have h : ⁅M, M⁆ = (⁅(⊤ : Subgroup ↥M), (⊤ : Subgroup ↥M)⁆).map M.subtype := by
    rw [Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype]
  rw [h]
  constructor
  · rintro ⟨c, hc, hcm⟩
    have : c = m := Subtype.ext hcm
    exact this ▸ hc
  · intro hm
    exact ⟨m, hm, rfl⟩

theorem uc22p22u_map_commutator (M : Subgroup G) :
    (⁅(⊤ : Subgroup ↥M), (⊤ : Subgroup ↥M)⁆).map (uc22p21cPi M) =
      ⁅(⊤ : Subgroup (Bar2 M)), (⊤ : Subgroup (Bar2 M))⁆ := by
  rw [Subgroup.map_commutator, Subgroup.map_top_of_surjective _ (uc22p21c_pi_surjective M)]

theorem uc22p22u_barImage_inf_commutator {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {M P : Subgroup G}
    (hP : CFSG.ABGLocalTools.IsSylowOf p P (F11.O2p p M)) :
    barImage M (P ⊓ ⁅M, M⁆) = CFSG.pCore p (Bar2 M) ⊓ ⁅(⊤ : Subgroup (Bar2 M)), (⊤ : Subgroup (Bar2 M))⁆ := by
  obtain ⟨hPM, hbar, -⟩ := uc22p22u_sylow_O2p hp hp2 hP
  haveI : Fact p.Prime := ⟨hp⟩
  have hPp : IsPGroup p ↥P := (CFSG.ABGLocalTools.isSylowOf_iff.1 hP).2.1
  apply le_antisymm
  · intro y hy
    obtain ⟨m, hm, rfl⟩ := uc22p21c_mem_barImage.1 hy
    refine ⟨hbar ▸ uc22p21c_mem_barImage.2 ⟨m, hm.1, rfl⟩, ?_⟩
    rw [← uc22p22u_map_commutator]
    exact ⟨m, (uc22p22u_mem_commutator_iff m).1 hm.2, rfl⟩
  · rintro y ⟨hy1, hy2⟩
    obtain ⟨x, hxP, rfl⟩ := uc22p21c_mem_barImage.1 (hbar ▸ hy1)
    rw [← uc22p22u_map_commutator] at hy2
    obtain ⟨c, hc, hcx⟩ := hy2
    have hz : x⁻¹ * c ∈ CFSG.pCore 2 ↥M := by
      refine (QuotientGroup.eq_one_iff _).1 ?_
      change uc22p21cPi M (x⁻¹ * c) = 1
      rw [map_mul, map_inv, hcx, inv_mul_cancel]
    obtain ⟨k, hk⟩ : ∃ k : ℕ, x ^ p ^ k = 1 := by
      obtain ⟨k, hk⟩ := hPp ⟨(x : G), hxP⟩
      have h1 : (x : G) ^ p ^ k = 1 := by
        have := congrArg (fun a : ↥P => (a : G)) hk
        simpa using this
      exact ⟨k, Subtype.ext (by simpa using h1)⟩
    obtain ⟨j, hj⟩ : ∃ j : ℕ, (x⁻¹ * c) ^ 2 ^ j = 1 := by
      obtain ⟨j, hj⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥M)) ⟨_, hz⟩
      exact ⟨j, congrArg Subtype.val hj⟩
    have hxc : x ∈ ⁅(⊤ : Subgroup ↥M), (⊤ : Subgroup ↥M)⁆ := by
      let q := QuotientGroup.mk' ⁅(⊤ : Subgroup ↥M), (⊤ : Subgroup ↥M)⁆
      have hqc : q c = 1 := (QuotientGroup.eq_one_iff _).2 hc
      have hqx : q x = q (x⁻¹ * c)⁻¹ := by
        rw [map_inv, map_mul, map_inv, hqc, mul_one, inv_inv]
      have h1 : orderOf (q x) ∣ p ^ k := orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hk, map_one])
      have h2 : orderOf (q x) ∣ 2 ^ j := by
        rw [hqx, map_inv, orderOf_inv]
        exact orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hj, map_one])
      have hcop : Nat.Coprime (p ^ k) (2 ^ j) :=
        Nat.Coprime.pow k j ((Nat.coprime_primes hp Nat.prime_two).2 hp2)
      have h3 : orderOf (q x) ∣ 1 := hcop ▸ Nat.dvd_gcd h1 h2
      have h4 : orderOf (q x) = 1 := Nat.dvd_one.1 h3
      exact (QuotientGroup.eq_one_iff _).1 (orderOf_eq_one_iff.1 h4)
    exact uc22p21c_mem_barImage.2 ⟨x, ⟨hxP, (uc22p22u_mem_commutator_iff x).2 hxc⟩, rfl⟩

theorem uc22p22u_le_pCoreOf {Γ : Type*} [Group Γ] {p : ℕ} (S T : Subgroup Γ) [hS : S.Normal]
    (hSp : IsPGroup p ↥S) (hST : S ≤ T) : S ≤ pCoreOf p T := by
  have hnorm : (S.subgroupOf T).Normal := hS.subgroupOf T
  have hpg : IsPGroup p ↥(S.subgroupOf T) := hSp.comap_subtype
  have hle : S.subgroupOf T ≤ CFSG.pCore p ↥T := le_sSup ⟨hnorm, hpg⟩
  intro b hb
  exact ⟨⟨b, hST hb⟩, hle (Subgroup.mem_subgroupOf.2 hb), rfl⟩

theorem uc22p22u_exists_phi {M X : Subgroup G} [hX : (X.subgroupOf M).Normal] (hO : pCoreOf 2 M ≤ X) :
    ∃ φ : Bar2 M →* ↥M ⧸ X.subgroupOf M, Function.Surjective φ ∧ φ.ker = barImage M X ∧
      ∀ m : ↥M, φ (uc22p21cPi M m) = (QuotientGroup.mk m : ↥M ⧸ X.subgroupOf M) := by
  haveI : (CFSG.pCore 2 ↥M).Normal := CFSG.pCore_normal
  have hle : CFSG.pCore 2 ↥M ≤ (QuotientGroup.mk' (X.subgroupOf M)).ker := by
    rw [QuotientGroup.ker_mk']
    intro m hm
    exact Subgroup.mem_subgroupOf.2 (hO ⟨m, hm, rfl⟩)
  refine ⟨QuotientGroup.lift (CFSG.pCore 2 ↥M) (QuotientGroup.mk' (X.subgroupOf M)) hle, ?_, ?_,
    fun m => rfl⟩
  · intro q
    obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective q
    exact ⟨QuotientGroup.mk m, rfl⟩
  · ext q
    obtain ⟨m, rfl⟩ := uc22p21c_pi_surjective M q
    rw [MonoidHom.mem_ker]
    change (QuotientGroup.mk m : ↥M ⧸ X.subgroupOf M) = 1 ↔ _
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    constructor
    · intro hm
      exact uc22p21c_mem_barImage.2 ⟨m, hm, rfl⟩
    · intro hm
      obtain ⟨m', hm', hmm⟩ := uc22p21c_mem_barImage.1 hm
      have h1 : m'⁻¹ * m ∈ CFSG.pCore 2 ↥M := by
        refine (QuotientGroup.eq_one_iff _).1 ?_
        change uc22p21cPi M (m'⁻¹ * m) = 1
        rw [map_mul, map_inv, hmm, inv_mul_cancel]
      have h2 : ((m'⁻¹ * m : ↥M) : G) ∈ X := hO ⟨_, h1, rfl⟩
      have h3 : (m : G) = (m' : G) * ((m'⁻¹ * m : ↥M) : G) := by simp
      rw [h3]
      exact X.mul_mem hm' h2

theorem uc22p22u_r1110_part1 (D : Data G) (h118 : R118W D) {V : Subgroup G} (hV : F11.Hyp11 D ⊥ V)
    [hNorm : ((F11.CTilde D.M ⊥ V).subgroupOf D.M).Normal] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {P : Subgroup G} (hP : CFSG.ABGLocalTools.IsSylowOf p P (F11.O2p p D.M)) :
    pCoreOf p ⁅(⊤ : Subgroup (F11.MBar11 D.M ⊥ V)), (⊤ : Subgroup (F11.MBar11 D.M ⊥ V))⁆ =
      F11.barImage11 D.M ⊥ V (P ⊓ ⁅D.M, D.M⁆) := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨hW, -⟩ := uc22p22u_hyp11_W D hV
  have hVc := uc22p22u_cTilde_bot D.M V
  have hO : pCoreOf 2 D.M ≤ F11.CTilde D.M ⊥ V := by
    rw [hVc]
    exact le_inf (uc22p21c_pCoreOf_le D.M) (uc22p22u_pCore_le_cent hW)
  have hn : D.M ≤ normalizer ((F11.CTilde D.M ⊥ V : Subgroup G) : Set G) := by
    rw [hVc]
    exact uc22p22u_normalizes_cent hW.1.1.2.2.1
  haveI hNn : (barImage D.M (F11.CTilde D.M ⊥ V)).Normal := uc22p22u_barImage_normal hn
  obtain ⟨φ, hφs, hφk, hφπ⟩ := uc22p22u_exists_phi (M := D.M) (X := F11.CTilde D.M ⊥ V) hO
  have hbar := uc22p22u_barImage_inf_commutator hp hp2 hP
  have key := uc22p22u_pCore_commutator_le_image φ hφs (barImage D.M (F11.CTilde D.M ⊥ V)) hφk p hp
    (h118 V hV)
  apply le_antisymm
  · intro b hb
    obtain ⟨y, hy, hφy⟩ := key b hb
    rw [← hbar] at hy
    obtain ⟨m, hm, rfl⟩ := uc22p21c_mem_barImage.1 hy
    rw [← hφy, hφπ]
    exact ⟨m, hm, rfl⟩
  · set T : Subgroup (F11.MBar11 D.M ⊥ V) := ⁅(⊤ : Subgroup (F11.MBar11 D.M ⊥ V)), ⊤⁆ with hT
    set S : Subgroup (F11.MBar11 D.M ⊥ V) := F11.barImage11 D.M ⊥ V (P ⊓ ⁅D.M, D.M⁆) with hS
    have hSφ : S = (CFSG.pCore p (Bar2 D.M) ⊓ ⁅(⊤ : Subgroup (Bar2 D.M)), ⊤⁆).map φ := by
      rw [← hbar]
      ext b
      constructor
      · rintro ⟨m, hm, rfl⟩
        exact ⟨uc22p21cPi D.M m, uc22p21c_mem_barImage.2 ⟨m, hm, rfl⟩, hφπ m⟩
      · rintro ⟨y, hy, rfl⟩
        obtain ⟨m, hm, rfl⟩ := uc22p21c_mem_barImage.1 hy
        exact ⟨m, hm, (hφπ m).symm⟩
    haveI : (CFSG.pCore p (Bar2 D.M) ⊓ ⁅(⊤ : Subgroup (Bar2 D.M)), ⊤⁆).Normal := by
      haveI : (CFSG.pCore p (Bar2 D.M)).Normal := CFSG.pCore_normal
      infer_instance
    haveI hSn : S.Normal := by
      rw [hSφ]
      exact Subgroup.Normal.map inferInstance φ hφs
    have hSle : S ≤ T := by
      rw [hSφ, hT, ← Subgroup.map_top_of_surjective φ hφs, ← Subgroup.map_commutator]
      exact Subgroup.map_mono inf_le_right
    have hSp : IsPGroup p ↥S := by
      have h0 : IsPGroup p ↥(CFSG.pCore p (Bar2 D.M) ⊓ ⁅(⊤ : Subgroup (Bar2 D.M)), ⊤⁆) :=
        (CFSG.pCore_isPGroup (p := p) (G := Bar2 D.M)).to_inf_left
      rw [hSφ]
      exact h0.map φ
    exact uc22p22u_le_pCoreOf S T hSp hSle

theorem uc22p22u_r1110_part2 (D : Data G) (h116 : R116W D) {V : Subgroup G} (hV : F11.Hyp11 D ⊥ V)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {P : Subgroup G}
    (hP : CFSG.ABGLocalTools.IsSylowOf p P (F11.O2p p D.M)) :
    IsCyclic ↥(P ⊓ F11.CTilde D.M ⊥ V) ∧ ⁅P ⊓ ⁅D.M, D.M⁆, P ⊓ F11.CTilde D.M ⊥ V⁆ = ⊥ := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨hPM, hbar, hP2⟩ := uc22p22u_sylow_O2p hp hp2 hP
  obtain ⟨hW, -⟩ := uc22p22u_hyp11_W D hV
  have hVc := uc22p22u_cTilde_bot D.M V
  have hn : D.M ≤ normalizer ((F11.CTilde D.M ⊥ V : Subgroup G) : Set G) := by
    rw [hVc]
    exact uc22p22u_normalizes_cent hW.1.1.2.2.1
  haveI hNn : (barImage D.M (F11.CTilde D.M ⊥ V)).Normal := uc22p22u_barImage_normal hn
  obtain ⟨hcyc, hcomm⟩ := h116 V hV
  set X₀ : Subgroup G := F11.CTilde D.M ⊥ V with hX₀
  set N : Subgroup (Bar2 D.M) := barImage D.M X₀ with hN
  set F : Subgroup (Bar2 D.M) := (CFSG.fittingSubgroup ↥N).map N.subtype with hF
  have hFcyc : IsCyclic ↥F := (uc22p22u_isCyclic_map_iff _ N.subtype_injective _).2 hcyc
  have hUM : P ⊓ X₀ ≤ D.M := inf_le_left.trans hPM
  have hA : ∀ x : ↥D.M, (x : G) ∈ P ⊓ X₀ → uc22p21cPi D.M x ∈ F := by
    intro x hx
    have h1 : uc22p21cPi D.M x ∈ CFSG.pCore p (Bar2 D.M) :=
      hbar ▸ uc22p21c_mem_barImage.2 ⟨x, hx.1, rfl⟩
    have h2 : uc22p21cPi D.M x ∈ N := uc22p21c_mem_barImage.2 ⟨x, hx.2, rfl⟩
    haveI : (CFSG.pCore p (Bar2 D.M)).Normal := CFSG.pCore_normal
    set R : Subgroup (Bar2 D.M) := CFSG.pCore p (Bar2 D.M) ⊓ N with hR
    haveI hRn : R.Normal := inferInstance
    have hRp : IsPGroup p ↥R := (CFSG.pCore_isPGroup (p := p) (G := Bar2 D.M)).to_inf_left
    have hRN : (R.subgroupOf N).Normal := hRn.subgroupOf N
    have hRp' : IsPGroup p ↥(R.subgroupOf N) := hRp.comap_subtype
    have hRnil : Group.IsNilpotent ↥(R.subgroupOf N) := hRp'.isNilpotent
    have hle : R.subgroupOf N ≤ CFSG.fittingSubgroup ↥N := le_sSup ⟨hRN, hRnil⟩
    exact ⟨⟨uc22p21cPi D.M x, h2⟩, hle (Subgroup.mem_subgroupOf.2 ⟨h1, h2⟩), rfl⟩
  have hker : ∀ a b : ↥(P ⊓ X₀), uc22p21cPi D.M (Subgroup.inclusion hUM a) =
      uc22p21cPi D.M (Subgroup.inclusion hUM b) → a = b := by
    intro a b hab
    have h1 : (Subgroup.inclusion hUM a)⁻¹ * Subgroup.inclusion hUM b ∈ CFSG.pCore 2 ↥D.M :=
      (QuotientGroup.eq_one_iff _).1 (by
        change uc22p21cPi D.M _ = 1
        rw [map_mul, map_inv, hab, inv_mul_cancel])
    have h2 : ((a : G))⁻¹ * (b : G) ∈ P ⊓ pCoreOf 2 D.M :=
      ⟨(P ⊓ X₀).mul_mem ((P ⊓ X₀).inv_mem a.2) b.2 |>.1, ⟨_, h1, rfl⟩⟩
    rw [hP2, Subgroup.mem_bot] at h2
    exact Subtype.ext (inv_mul_eq_one.1 h2)
  refine ⟨?_, ?_⟩
  · let g : ↥(P ⊓ X₀) →* ↥F := ((uc22p21cPi D.M).comp (Subgroup.inclusion hUM)).codRestrict F
      fun a => hA (Subgroup.inclusion hUM a) a.2
    haveI := hFcyc
    exact isCyclic_of_injective g fun a b hab => hker a b (congrArg Subtype.val hab)
  · rw [← le_bot_iff, Subgroup.commutator_le]
    intro q hq u hu
    have hqM : q ∈ D.M := hPM hq.1
    have huM : u ∈ D.M := hUM hu
    have hq' : uc22p21cPi D.M ⟨q, hqM⟩ ∈ ⁅(⊤ : Subgroup (Bar2 D.M)), (⊤ : Subgroup (Bar2 D.M))⁆ := by
      rw [← uc22p22u_map_commutator]
      exact ⟨⟨q, hqM⟩, (uc22p22u_mem_commutator_iff ⟨q, hqM⟩).1 hq.2, rfl⟩
    have hcen := Subgroup.mem_centralizer_iff.1 (hcomm hq') _ (hA ⟨u, huM⟩ hu)
    have h1 : ⁅(⟨q, hqM⟩ : ↥D.M), ⟨u, huM⟩⁆ ∈ CFSG.pCore 2 ↥D.M := by
      refine (QuotientGroup.eq_one_iff _).1 ?_
      change uc22p21cPi D.M _ = 1
      rw [map_commutatorElement]
      exact commutatorElement_eq_one_iff_commute.2 hcen.symm
    have h2 : ⁅q, u⁆ ∈ P ⊓ pCoreOf 2 D.M := by
      refine ⟨?_, ⟨_, h1, rfl⟩⟩
      have hu' : u ∈ P := hu.1
      have : ⁅q, u⁆ = q * u * q⁻¹ * u⁻¹ := rfl
      rw [this]
      exact P.mul_mem (P.mul_mem (P.mul_mem hq.1 hu') (P.inv_mem hq.1)) (P.inv_mem hu')
    rw [hP2] at h2
    exact h2

end CFSG.LocalAnalysis.UniquenessCase.UC22
