module

public import CFSG.Quasithin.Vol2.Ch3E213MKer

public section

namespace CFSG.Quasithin.Res2

namespace WGen

open CFSG.Open CFSG.QuasithinUnique B6 E2

variable {G : Type} [Group G] {X T M V : Subgroup G} {g : G}

theorem conj_eq_of_mem_Z (h : E2.Pair X T M V g) {z x : G} (hz : z ∈ V ⊓ conjSub g V)
    (hx : x ∈ X) : x * z * x⁻¹ = z := by
  rw [← h.mem_center hz hx]
  group

theorem P_le_kerIn (h : E2.Pair X T M V g) :
    (kerIn M X ⊓ V) ⊔ conjSub g (kerIn M X ⊓ V) ≤ kerIn M X := by
  refine sup_le inf_le_left ?_
  calc conjSub g (kerIn M X ⊓ V) ≤ conjSub g (kerIn M X) := (conjSub g).monotone inf_le_left
    _ = kerIn M X := conjSub_eq_self (le_normalizer_kerIn M X h.mem)

variable [Finite G]

theorem card_P_eq (h : E2.Pair X T M V g) (hBZ : (V ⊓ conjSub g V).relIndex (kerIn M X ⊓ V) = 4) :
    Nat.card ↥((kerIn M X ⊓ V) ⊔ conjSub g (kerIn M X ⊓ V)) =
      16 * Nat.card ↥(V ⊓ conjSub g V) := by
  have h1 := Subgroup.relIndex_mul_card (V ⊓ conjSub g V)
    ((kerIn M X ⊓ V) ⊔ conjSub g (kerIn M X ⊓ V))
  rw [inf_eq_left.2 h.inf_conj_le_P, Ch3E213M.relIndex_P_eq h, hBZ] at h1
  rw [← h1]
  norm_num

theorem sixteen_mul_card_le (h : E2.Pair X T M V g) {c : G} (hcX : c ∈ X) (hc : orderOf c = 5)
    {S : Subgroup G} (hSP : S ≤ (kerIn M X ⊓ V) ⊔ conjSub g (kerIn M X ⊓ V))
    (hXS : X ≤ Subgroup.normalizer (S : Set G)) (hne : ∃ s ∈ S, c * s * c⁻¹ ≠ s) :
    16 * Nat.card ↥(S ⊓ Subgroup.centralizer ({c} : Set G)) ≤ Nat.card ↥S := by
  have hS2 : IsPGroup 2 S :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X).to_le (hSP.trans h.P_le_pCoreOf)
  obtain ⟨d, hd⟩ := IsPGroup.iff_card.mp hS2
  set c' : Subgroup.normalizer (S : Set G) := ⟨c, hXS hcX⟩ with hc'
  have hc'ord : orderOf c' = 5 ^ (0 + 1) := by rw [hc', Subgroup.orderOf_mk, hc]; norm_num
  have hcoe : ((c' ^ 5 ^ 0 : Subgroup.normalizer (S : Set G)) : G) = c := by
    rw [pow_zero, pow_one]
  have hne' : S.normalizerMonoidHom (c' ^ 5 ^ 0) ≠ 1 := by
    intro h1
    obtain ⟨s, hs, hsne⟩ := hne
    have h2 := congrArg Subtype.val (DFunLike.congr_fun h1 ⟨s, hs⟩)
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe, hcoe, MulAut.one_apply] at h2
    exact hsne h2
  have hfix : ∀ z ∈ (S ⊓ Subgroup.centralizer ({c} : Set G)).subgroupOf S,
      S.normalizerMonoidHom (c' ^ 5 ^ 0) z = z := by
    intro z hz
    apply Subtype.ext
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe, hcoe]
    have hzc := Subgroup.mem_centralizer_iff.1 (Subgroup.mem_subgroupOf.1 hz).2 c rfl
    calc c * (z : G) * c⁻¹ = (z : G) * c * c⁻¹ := by rw [hzc]
      _ = z := by group
  obtain ⟨m, hm0, hmZ, hmdvd⟩ := Ch3E213M.exists_two_pow_of_orderOf S.normalizerMonoidHom hd
    (ℓ := 5) (a := 0) (by norm_num) (by norm_num) hc'ord hne'
    ((S ⊓ Subgroup.centralizer ({c} : Set G)).subgroupOf S) hfix
  have hm4 : 4 ≤ m := by
    by_contra hlt
    have : m < 4 := by omega
    interval_cases m <;> simp at hmdvd
  have hcard : Nat.card ((S ⊓ Subgroup.centralizer ({c} : Set G)).subgroupOf S) =
      Nat.card ↥(S ⊓ Subgroup.centralizer ({c} : Set G)) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  rw [hcard] at hmZ
  calc 16 * Nat.card ↥(S ⊓ Subgroup.centralizer ({c} : Set G))
      ≤ 2 ^ m * Nat.card ↥(S ⊓ Subgroup.centralizer ({c} : Set G)) :=
        Nat.mul_le_mul_right _ (by
          calc 16 = 2 ^ 4 := by norm_num
            _ ≤ 2 ^ m := Nat.pow_le_pow_right two_pos hm4)
    _ ≤ 2 ^ d := hmZ
    _ = Nat.card ↥S := hd.symm

theorem exists_not_comm (h : E2.Pair X T M V g) (hchar : CharTwo X) {c : G} (hcX : c ∈ X)
    (hc : orderOf c = 5) :
    ∃ p ∈ (kerIn M X ⊓ V) ⊔ conjSub g (kerIn M X ⊓ V), c * p * c⁻¹ ≠ p := by
  by_contra hcon
  push Not at hcon
  obtain ⟨n, hn⟩ := Ch3E213M.isTwo_of_centralizes h hchar hcX (fun p hp => by
    rw [hcon p hp]
    simp only [mul_inv_cancel]
    exact (V ⊓ conjSub g V).one_mem)
  have h5 : 5 ∣ 2 ^ n := hc ▸ orderOf_dvd_of_pow_eq_one hn
  have := (Nat.Prime.dvd_of_dvd_pow (by norm_num) h5)
  omega

theorem mem_Z_of_commute (h : E2.Pair X T M V g) (hchar : CharTwo X)
    (hBZ : (V ⊓ conjSub g V).relIndex (kerIn M X ⊓ V) = 4) {c : G} (hcX : c ∈ X)
    (hc : orderOf c = 5) {p : G} (hp : p ∈ (kerIn M X ⊓ V) ⊔ conjSub g (kerIn M X ⊓ V))
    (hpc : c * p = p * c) : p ∈ V ⊓ conjSub g V := by
  set P := (kerIn M X ⊓ V) ⊔ conjSub g (kerIn M X ⊓ V) with hP
  set Z := V ⊓ conjSub g V with hZ
  have hZP : Z ≤ P := h.inf_conj_le_P
  have h16 := sixteen_mul_card_le h hcX hc (S := P) le_rfl h.le_normalizer_P
    (exists_not_comm h hchar hcX hc)
  rw [card_P_eq h hBZ] at h16
  have hZC : Z ≤ P ⊓ Subgroup.centralizer ({c} : Set G) := by
    refine le_inf hZP (fun z hz => ?_)
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact (h.mem_center hz hcX).symm
  have hcard : Nat.card ↥(P ⊓ Subgroup.centralizer ({c} : Set G)) ≤ Nat.card ↥Z :=
    Nat.le_of_mul_le_mul_left h16 (by norm_num : 0 < 16)
  have heq : Z = P ⊓ Subgroup.centralizer ({c} : Set G) := Subgroup.eq_of_le_of_card_ge hZC hcard
  have hpC : p ∈ P ⊓ Subgroup.centralizer ({c} : Set G) := by
    refine ⟨hp, ?_⟩
    show p ∈ Subgroup.centralizer ({c} : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact hpc
  rw [heq]
  exact hpC

theorem eq_or_eq_P (h : E2.Pair X T M V g) (hchar : CharTwo X)
    (hBZ : (V ⊓ conjSub g V).relIndex (kerIn M X ⊓ V) = 4) {c : G} (hcX : c ∈ X)
    (hc : orderOf c = 5) {S : Subgroup G} (hZS : V ⊓ conjSub g V ≤ S)
    (hSP : S ≤ (kerIn M X ⊓ V) ⊔ conjSub g (kerIn M X ⊓ V))
    (hXS : X ≤ Subgroup.normalizer (S : Set G)) :
    S = V ⊓ conjSub g V ∨ S = (kerIn M X ⊓ V) ⊔ conjSub g (kerIn M X ⊓ V) := by
  by_cases hne : ∃ s ∈ S, c * s * c⁻¹ ≠ s
  · right
    have h16 := sixteen_mul_card_le h hcX hc hSP hXS hne
    have hZC : V ⊓ conjSub g V ≤ S ⊓ Subgroup.centralizer ({c} : Set G) := by
      refine le_inf hZS (fun z hz => ?_)
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact (h.mem_center hz hcX).symm
    have h1 := Subgroup.card_le_of_le hZC
    have h2 := card_P_eq h hBZ
    exact Subgroup.eq_of_le_of_card_ge hSP (by omega)
  · left
    push Not at hne
    refine le_antisymm (fun s hs => ?_) hZS
    refine mem_Z_of_commute h hchar hBZ hcX hc (hSP hs) ?_
    have := hne s hs
    calc c * s = c * s * c⁻¹ * c := by group
      _ = s * c := by rw [this]

theorem exists_mem_P_centralizes (h : E2.Pair X T M V g) (hJ : IsPGroup 2 ↥(kerIn M X))
    (hBZ : (V ⊓ conjSub g V).relIndex (kerIn M X ⊓ V) = 4) :
    ∃ p ∈ (kerIn M X ⊓ V) ⊔ conjSub g (kerIn M X ⊓ V), p ∉ V ⊓ conjSub g V ∧
      ∀ j ∈ kerIn M X, p⁻¹ * j * p * j⁻¹ ∈ V ⊓ conjSub g V := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set J := kerIn M X with hJdef
  set P := (kerIn M X ⊓ V) ⊔ conjSub g (kerIn M X ⊓ V) with hPdef
  set Z := V ⊓ conjSub g V with hZdef
  have hJX : J ≤ X := kerIn_le.trans h.le_X
  have hPJ : P ≤ J := P_le_kerIn h
  have hZP : Z ≤ P := h.inf_conj_le_P
  have hZJ : Z ≤ J := hZP.trans hPJ
  have hZn : (Z.subgroupOf J).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hZJ).2 (hJX.trans h.le_normalizer_Z)
  have hPn : (P.subgroupOf J).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hPJ).2 (hJX.trans h.le_normalizer_P)
  set π : ↥J →* ↥J ⧸ Z.subgroupOf J := QuotientGroup.mk' (Z.subgroupOf J) with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hN₁ : ((P.subgroupOf J).map π).Normal := hPn.map π hπs
  obtain ⟨p₀, hp₀P, hp₀Z⟩ : ∃ p ∈ P, p ∉ Z := by
    by_contra hcon
    push Not at hcon
    have hPZ : P ≤ Z := hcon
    have heq : P = Z := le_antisymm hPZ hZP
    have h1 := card_P_eq h hBZ
    rw [← hPdef, ← hZdef, heq] at h1
    have : 0 < Nat.card ↥Z := Nat.card_pos
    omega
  have hbot : (P.subgroupOf J).map π ≠ ⊥ := by
    intro hb
    have hmem : π ⟨p₀, hPJ hp₀P⟩ ∈ (P.subgroupOf J).map π :=
      ⟨⟨p₀, hPJ hp₀P⟩, Subgroup.mem_subgroupOf.2 hp₀P, rfl⟩
    rw [hb, Subgroup.mem_bot, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
      Subgroup.mem_subgroupOf] at hmem
    exact hp₀Z hmem
  have hK2 : IsPGroup 2 (↥J ⧸ Z.subgroupOf J) := hJ.of_surjective π hπs
  have hnil : Group.IsNilpotent (↥J ⧸ Z.subgroupOf J) := hK2.isNilpotent
  have hc := Group.IsNilpotent.inf_center_ne_bot_of_normal hbot
  obtain ⟨n, hn⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hc
  obtain ⟨y, hy, hyn⟩ := Subgroup.mem_map.1 n.2.1
  have hyP : ((y : ↥J) : G) ∈ P := Subgroup.mem_subgroupOf.1 hy
  refine ⟨(y : G), hyP, ?_, ?_⟩
  · intro hyZ
    apply hn
    apply Subtype.ext
    show (n : ↥J ⧸ Z.subgroupOf J) = 1
    rw [← hyn, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact Subgroup.mem_subgroupOf.2 hyZ
  · intro j hj
    have hcomm := Subgroup.mem_center_iff.1 n.2.2 (π ⟨j⁻¹, J.inv_mem hj⟩)
    rw [← hyn, hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, ← QuotientGroup.mk_mul,
      ← QuotientGroup.mk_mul, QuotientGroup.eq, Subgroup.mem_subgroupOf] at hcomm
    simpa [mul_assoc] using hcomm

theorem commutator_kerIn_mem_Z (h : E2.Pair X T M V g) (hchar : CharTwo X)
    (hJ : IsPGroup 2 ↥(kerIn M X)) (hcard : (kerIn M X).relIndex X = 60)
    (hBZ : (V ⊓ conjSub g V).relIndex (kerIn M X ⊓ V) = 4) :
    ∀ p ∈ (kerIn M X ⊓ V) ⊔ conjSub g (kerIn M X ⊓ V), ∀ j ∈ kerIn M X,
      p⁻¹ * j * p * j⁻¹ ∈ V ⊓ conjSub g V := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  set J := kerIn M X with hJdef
  set P := (kerIn M X ⊓ V) ⊔ conjSub g (kerIn M X ⊓ V) with hPdef
  set Z := V ⊓ conjSub g V with hZdef
  have hJX : J ≤ X := kerIn_le.trans h.le_X
  have hPJ : P ≤ J := P_le_kerIn h
  have hZP : Z ≤ P := h.inf_conj_le_P
  have hPX : P ≤ X := hPJ.trans hJX
  have h5 : 5 ∣ Nat.card ↥X :=
    (show 5 ∣ (kerIn M X).relIndex X by rw [hcard]; norm_num).trans
      (Subgroup.relIndex_dvd_card _ _)
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' 5 h5
  have hcX : (c : G) ∈ X := c.2
  have hco : orderOf (c : G) = 5 := by rw [Subgroup.orderOf_coe, hc]
  have hZc : ∀ z ∈ Z, ∀ x ∈ X, x⁻¹ * z * x = z := fun z hz x hx => by
    simpa using conj_eq_of_mem_Z h hz (X.inv_mem hx)
  let C : Subgroup G :=
    { carrier := {p | p ∈ P ∧ ∀ j ∈ J, p⁻¹ * j * p * j⁻¹ ∈ Z}
      one_mem' := ⟨P.one_mem, fun j _ => by simp⟩
      mul_mem' := by
        rintro p p' ⟨hp, hpj⟩ ⟨hp', hp'j⟩
        refine ⟨P.mul_mem hp hp', fun j hj => ?_⟩
        have e : (p * p')⁻¹ * j * (p * p') * j⁻¹ =
            p'⁻¹ * (p⁻¹ * j * p * j⁻¹) * p' * (p'⁻¹ * j * p' * j⁻¹) := by group
        rw [e, hZc _ (hpj j hj) _ (hPX hp')]
        exact Z.mul_mem (hpj j hj) (hp'j j hj)
      inv_mem' := by
        rintro p ⟨hp, hpj⟩
        refine ⟨P.inv_mem hp, fun j hj => ?_⟩
        have e : p⁻¹⁻¹ * j * p⁻¹ * j⁻¹ = p * (p⁻¹ * j * p * j⁻¹)⁻¹ * p⁻¹ := by group
        have hz := Z.inv_mem (hpj j hj)
        rw [e, conj_eq_of_mem_Z h hz (hPX hp)]
        exact hz }
  have hZC : Z ≤ C := by
    intro z hz
    refine ⟨hZP hz, fun j hj => ?_⟩
    have := h.mem_center hz (hJX hj)
    have e : z⁻¹ * j * z * j⁻¹ = 1 := by
      calc z⁻¹ * j * z * j⁻¹ = z⁻¹ * (j * z) * j⁻¹ := by group
        _ = 1 := by rw [← this]; group
    rw [e]
    exact Z.one_mem
  have hCP : C ≤ P := fun p hp => hp.1
  have hXC : X ≤ Subgroup.normalizer (C : Set G) := by
    have key : ∀ x ∈ X, ∀ p ∈ C, x * p * x⁻¹ ∈ C := by
      rintro x hx p ⟨hp, hpj⟩
      refine ⟨?_, fun j hj => ?_⟩
      · exact (Subgroup.mem_normalizer_iff.mp (h.le_normalizer_P hx) p).mp hp
      · have hj' : x⁻¹ * j * x ∈ J := by
          have := (Subgroup.mem_normalizer_iff.mp (le_normalizer_kerIn M X (X.inv_mem hx)) j).mp hj
          simpa using this
        have e : (x * p * x⁻¹)⁻¹ * j * (x * p * x⁻¹) * j⁻¹ =
            x * (p⁻¹ * (x⁻¹ * j * x) * p * (x⁻¹ * j * x)⁻¹) * x⁻¹ := by group
        rw [e, conj_eq_of_mem_Z h (hpj _ hj') hx]
        exact hpj _ hj'
    intro x hx
    exact mem_normalizer_of_forall_mem (key x hx) (fun p hp => by
      simpa using key x⁻¹ (X.inv_mem hx) p hp)
  have hcases := eq_or_eq_P h hchar hBZ hcX hco (S := C) hZC hCP hXC
  obtain ⟨p₀, hp₀P, hp₀Z, hp₀j⟩ := exists_mem_P_centralizes h hJ hBZ
  have hp₀C : p₀ ∈ C := ⟨hp₀P, hp₀j⟩
  have hCP' : C = P := by
    rcases hcases with hC | hC
    · exact absurd (hC ▸ hp₀C) hp₀Z
    · exact hC
  intro p hp j hj
  have hpC : p ∈ C := hCP' ▸ hp
  exact hpC.2 j hj

end WGen

end CFSG.Quasithin.Res2
