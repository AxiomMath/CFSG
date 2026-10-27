module

public import CFSG.Quasithin.Background.S1567Z4
public import CFSG.Quasithin.Background.S1567Z6
public import CFSG.Quasithin.EmptyFaithful.S153Cases

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open scoped commutatorElement Pointwise

namespace S1567

section O2

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ E : Subgroup G} {t : G}

theorem relIndex_two_pow_of_forall_pow_mem {K D : Subgroup G} (hKD : K ≤ D)
    (hn : D ≤ Subgroup.normalizer (K : Set G)) (h : ∀ d ∈ D, ∃ n : ℕ, d ^ 2 ^ n ∈ K) :
    ∃ k : ℕ, K.relIndex D = 2 ^ k := by
  have hN : (K.subgroupOf D).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hKD).mpr hn
  have hp : IsPGroup 2 (↥D ⧸ K.subgroupOf D) := by
    intro x
    obtain ⟨d, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨k, hk⟩ := h d d.2
    refine ⟨k, ?_⟩
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact hk
  obtain ⟨k, hk⟩ := hp.exists_card_eq
  exact ⟨k, hk⟩

theorem le_M_of_normal_two_quotient (k : Ctx67 G T Mc M V₁ V₂ E t) {D : Subgroup G}
    (hDC : D ≤ Subgroup.centralizer (E : Set G))
    (hDn : Subgroup.normalizer (E : Set G) ≤ Subgroup.normalizer (D : Set G))
    (hKD : K167 T M E ≤ D) (hD2 : ∀ d ∈ D, ∃ n : ℕ, d ^ 2 ^ n ∈ K167 T M E) : D ≤ M := by
  have hCN : Subgroup.centralizer (E : Set G) ≤ Subgroup.normalizer (E : Set G) :=
    Subgroup.centralizer_le_normalizer _
  have hsyl : IsSylowTwoOf (T ⊓ Subgroup.centralizer (E : Set G) ⊓ D) D :=
    A4.isSylowTwoOf_inf_normal (isSylowTwoOf_SE k) hDC (hCN.trans hDn)
  have hnorm : D ≤ Subgroup.normalizer (K167 T M E : Set G) := fun d hd =>
    normalizer_le_normalizer_K167 T M E (hCN (hDC hd))
  have hpow := relIndex_two_pow_of_forall_pow_mem hKD hnorm hD2
  have hodd : Odd ((T ⊓ Subgroup.centralizer (E : Set G) ⊓ D).relIndex D) := by
    have := isSylowTwoOf_odd_relIndex hsyl
    exact Nat.odd_iff.mpr (by omega)
  have hsup := sup_eq_of_relIndex_two_pow_of_odd hKD inf_le_right hpow hodd
  rw [← hsup]
  exact sup_le ((K167_le_M_inf_normalizer k).trans inf_le_left)
    ((inf_le_left.trans inf_le_left).trans k.c.hyp.T_le)

theorem exists_YE_move_quot (h113 : StageLemma14113) (k : Ctx67 G T Mc M V₁ V₂ E t) :
    ∃ y ∈ YE153 Mc M E, (∃ v ∈ VZ T M, ⁅y, v⁆ ∉ E) ∧ ∀ v ∈ VZ T M, ⁅y ^ 3, v⁆ ∈ E := by
  have hcube : ∀ y ∈ Y153 Mc M, y ^ 3 ∈ Subgroup.centralizer (VZ T M : Set G) := by
    intro y hy
    have h1 := Hyp153.pow_three_mem_pCoreOf_Y153 h113 k.c.hyp hy
    rw [k.r49.case_one.1] at h1
    exact h1.2
  have hYEY : YE153 Mc M E ≤ Y153 Mc M := (oTwoUpper_le _).trans inf_le_left
  have hex : ∃ y ∈ YE153 Mc M E, ∃ v ∈ VZ T M, ⁅y, v⁆ ∉ E := by
    by_contra hno
    push Not at hno
    have hle : ⁅VZ T M, YE153 Mc M E⁆ ≤ E := by
      rw [Subgroup.commutator_le]
      intro v hv y hy
      rw [← commutatorElement_inv]
      exact E.inv_mem (hno y hy v hv)
    rw [k.r66.V_comm] at hle
    have := Subgroup.card_le_of_le hle
    rw [k.c.hyp.card_VZ, k.L.card_eq] at this
    omega
  obtain ⟨y, hy, hv⟩ := hex
  refine ⟨y, hy, hv, fun v hv' => ?_⟩
  have h1 : v * y ^ 3 = y ^ 3 * v := Subgroup.mem_centralizer_iff.mp (hcube y (hYEY hy)) v hv'
  rw [commutatorElement_eq_one_iff_mul_comm.mpr h1.symm]
  exact E.one_mem

theorem le_K167_of_normal_two_quotient (h113 : StageLemma14113) (k : Ctx67 G T Mc M V₁ V₂ E t)
    {D : Subgroup G} (hDC : D ≤ Subgroup.centralizer (E : Set G))
    (hDn : Subgroup.normalizer (E : Set G) ≤ Subgroup.normalizer (D : Set G))
    (hKD : K167 T M E ≤ D) (hD2 : ∀ d ∈ D, ∃ n : ℕ, d ^ 2 ^ n ∈ K167 T M E) :
    D ≤ K167 T M E := by
  have hCN : Subgroup.centralizer (E : Set G) ≤ Subgroup.normalizer (E : Set G) :=
    Subgroup.centralizer_le_normalizer _
  have hDM : D ≤ M := le_M_of_normal_two_quotient k hDC hDn hKD hD2
  have hMV : M ≤ Subgroup.normalizer (VZ T M : Set G) := k.c.hyp.le_normalizer
  have hDN : D ≤ Subgroup.normalizer (VZ T M : Set G) ⊓ Subgroup.normalizer (E : Set G) :=
    fun d hd => ⟨hMV (hDM hd), hCN (hDC hd)⟩
  obtain ⟨y, hyYE, ⟨v₀, hv₀, hv₀E⟩, hy3⟩ := exists_YE_move_quot h113 k
  have hyE : y ∈ Subgroup.normalizer (E : Set G) := ((oTwoUpper_le _).trans inf_le_right) hyYE
  have hyM : y ∈ M := ((oTwoUpper_le _).trans (inf_le_left.trans (Y153_le Mc M))) hyYE
  have hyN : y ∈ Subgroup.normalizer (VZ T M : Set G) ⊓ Subgroup.normalizer (E : Set G) :=
    ⟨hMV hyM, hyE⟩
  have key : ∀ d ∈ D, ∀ v ∈ VZ T M, ⁅d, v⁆ ∈ E :=
    comm_le_of_normal_two_group k.c.hyp.elemAbelian k.L.le_V k.c.hyp.card_VZ k.L.card_eq hDN hyN
      (fun d hd => (Subgroup.mem_normalizer_iff.mp (hDn hyE) d).mp hd)
      (fun d hd => by
        obtain ⟨n, hn⟩ := hD2 d hd
        exact ⟨n, fun v hv => hn.2 v (VZ_le_VE67 hv)⟩)
      ⟨v₀, hv₀, hv₀E⟩ hy3
  let W : Subgroup G :=
    { carrier := {x | x ∈ Subgroup.normalizer (E : Set G) ∧ ∀ d ∈ D, d * x * d⁻¹ * x⁻¹ ∈ E}
      one_mem' := ⟨Subgroup.one_mem _, fun d _ => by simp⟩
      mul_mem' := by
        rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
        refine ⟨Subgroup.mul_mem _ ha hb, fun d hd => ?_⟩
        have e : d * (a * b) * d⁻¹ * (a * b)⁻¹ =
            (d * a * d⁻¹ * a⁻¹) * (a * (d * b * d⁻¹ * b⁻¹) * a⁻¹) := by group
        rw [e]
        exact E.mul_mem (ha' d hd) ((Subgroup.mem_normalizer_iff.mp ha _).mp (hb' d hd))
      inv_mem' := by
        rintro a ⟨ha, ha'⟩
        refine ⟨Subgroup.inv_mem _ ha, fun d hd => ?_⟩
        have e : d * a⁻¹ * d⁻¹ * a⁻¹⁻¹ = a⁻¹ * (d * a * d⁻¹ * a⁻¹)⁻¹ * a := by group
        rw [e]
        have h1 := (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer _).inv_mem ha) _).mp
          (E.inv_mem (ha' d hd))
        simpa using h1 }
  have hVW : VE67 T M E ≤ W := by
    refine conjClosure_le fun g hg z hz => ?_
    have hgi : g⁻¹ ∈ Subgroup.normalizer (E : Set G) := (Subgroup.normalizer _).inv_mem hg
    refine ⟨(Subgroup.normalizer _).mul_mem ((Subgroup.normalizer _).mul_mem hg
      (VZ_le_normalizer_E k hz)) hgi, fun d hd => ?_⟩
    have hd' : g⁻¹ * d * g ∈ D := by
      have := (Subgroup.mem_normalizer_iff.mp (hDn hgi) d).mp hd
      simpa using this
    have h1 := key _ hd' z hz
    have h2 : g * (g⁻¹ * d * g * z * (g⁻¹ * d * g)⁻¹ * z⁻¹) * g⁻¹ ∈ E :=
      (Subgroup.mem_normalizer_iff.mp hg _).mp h1
    have e : d * (g * z * g⁻¹) * d⁻¹ * (g * z * g⁻¹)⁻¹ =
        g * (g⁻¹ * d * g * z * (g⁻¹ * d * g)⁻¹ * z⁻¹) * g⁻¹ := by group
    rw [e]
    exact h2
  intro d hd
  exact ⟨hDC hd, fun v hv => (hVW hv).2 d hd⟩

omit [Finite G] in
theorem exists_mul_of_mem_sup {K Q : Subgroup G} (h : Q ≤ Subgroup.normalizer (K : Set G)) {d : G}
    (hd : d ∈ K ⊔ Q) : ∃ κ ∈ K, ∃ q ∈ Q, d = κ * q := by
  let S : Subgroup G :=
    { carrier := {x | ∃ κ ∈ K, ∃ q ∈ Q, x = κ * q}
      one_mem' := ⟨1, K.one_mem, 1, Q.one_mem, by simp⟩
      mul_mem' := by
        rintro _ _ ⟨κ₁, hκ₁, q₁, hq₁, rfl⟩ ⟨κ₂, hκ₂, q₂, hq₂, rfl⟩
        exact ⟨κ₁ * (q₁ * κ₂ * q₁⁻¹),
          K.mul_mem hκ₁ ((Subgroup.mem_normalizer_iff.mp (h hq₁) κ₂).mp hκ₂), q₁ * q₂,
          Q.mul_mem hq₁ hq₂, by group⟩
      inv_mem' := by
        rintro _ ⟨κ, hκ, q, hq, rfl⟩
        refine ⟨q⁻¹ * κ⁻¹ * q, ?_, q⁻¹, Q.inv_mem hq, by group⟩
        have := (Subgroup.mem_normalizer_iff.mp (h (Q.inv_mem hq)) κ⁻¹).mp (K.inv_mem hκ)
        simpa using this }
  exact (sup_le (fun κ hκ => ⟨κ, hκ, 1, Q.one_mem, by simp⟩)
    (fun q hq => ⟨1, K.one_mem, q, hq, by simp⟩) : K ⊔ Q ≤ S) hd

omit [Finite G] in
theorem exists_pow_mem_of_mul {K Q : Subgroup G} (h : Q ≤ Subgroup.normalizer (K : Set G)) {κ q : G}
    (hκ : κ ∈ K) (hq : q ∈ Q) (hq2 : ∃ n : ℕ, q ^ 2 ^ n = 1) : ∃ n : ℕ, (κ * q) ^ 2 ^ n ∈ K := by
  obtain ⟨n, hn⟩ := hq2
  have key : ∀ m : ℕ, ∃ κ' ∈ K, (κ * q) ^ m = κ' * q ^ m := by
    intro m
    induction m with
    | zero => exact ⟨1, K.one_mem, by simp⟩
    | succ m ih =>
      obtain ⟨κ', hκ', he⟩ := ih
      have hqm : q ^ m ∈ Q := Q.pow_mem hq m
      refine ⟨κ' * (q ^ m * κ * (q ^ m)⁻¹), K.mul_mem hκ'
        ((Subgroup.mem_normalizer_iff.mp (h hqm) κ).mp hκ), ?_⟩
      rw [pow_succ, he]
      group
  obtain ⟨κ', hκ', he⟩ := key (2 ^ n)
  exact ⟨n, by rw [he, hn, mul_one]; exact hκ'⟩

theorem QE_le_K167 (h113 : StageLemma14113) (k : Ctx67 G T Mc M V₁ V₂ E t) :
    QE153 E ≤ K167 T M E := by
  have hQC : QE153 E ≤ Subgroup.centralizer (E : Set G) := k.r66.QE_le
  have hKN := normalizer_le_normalizer_K167 T M E
  have hQN : Subgroup.normalizer (E : Set G) ≤ Subgroup.normalizer (QE153 E : Set G) :=
    le_normalizer_pCoreOf 2 _
  have hQG : QE153 E ≤ Subgroup.normalizer (E : Set G) := pCoreOf_le 2 _
  have hQK : QE153 E ≤ Subgroup.normalizer (K167 T M E : Set G) := hQG.trans hKN
  have hQ2 : ∀ q ∈ QE153 E, ∃ n : ℕ, q ^ 2 ^ n = 1 := by
    intro q hq
    obtain ⟨n, hn⟩ := pCoreOf_isPGroup 2 _ ⟨q, hq⟩
    exact ⟨n, by simpa using congrArg Subtype.val hn⟩
  have hD := le_K167_of_normal_two_quotient h113 k (D := K167 T M E ⊔ QE153 E)
    (sup_le K167_le_centralizer hQC) (B2F.le_normalizer_sup hKN hQN) le_sup_left (fun d hd => by
      obtain ⟨κ, hκ, q, hq, rfl⟩ := exists_mul_of_mem_sup hQK hd
      exact exists_pow_mem_of_mul hQK hκ hq (hQ2 q hq))
  exact le_sup_right.trans hD

theorem pCoreOf_Mc_inf_CE_le_K167 (h113 : StageLemma14113) (k : Ctx67 G T Mc M V₁ V₂ E t) :
    pCoreOf 2 Mc ⊓ Subgroup.centralizer (E : Set G) ≤ K167 T M E := by
  have hCN : Subgroup.centralizer (E : Set G) ≤ Subgroup.normalizer (E : Set G) :=
    Subgroup.centralizer_le_normalizer _
  set P : Subgroup G := pCoreOf 2 Mc ⊓ Subgroup.centralizer (E : Set G) with hP
  have hCM : Subgroup.centralizer (E : Set G) ≤ Mc := k.r66.centralizer_le_mc
  have hPn : Subgroup.centralizer (E : Set G) ≤ Subgroup.normalizer (P : Set G) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have h1 := Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 Mc (hCM hx)) y
    have h2 := Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer hx) y
    simp only [hP, Subgroup.mem_inf]
    exact ⟨fun ⟨a, b⟩ => ⟨h1.mp a, h2.mp b⟩, fun ⟨a, b⟩ => ⟨h1.mpr a, h2.mpr b⟩⟩
  have hPp : IsPGroup 2 ↥P := (pCoreOf_isPGroup 2 Mc).to_inf_left
  have hPC : P ≤ pCoreOf 2 (Subgroup.centralizer (E : Set G)) :=
    le_pCoreOf_of_le_normalizer 2 inf_le_right hPn hPp
  have hCC : Subgroup.normalizer (E : Set G) ≤
      Subgroup.normalizer (pCoreOf 2 (Subgroup.centralizer (E : Set G)) : Set G) :=
    (normalizer_le_normalizer_CE E).trans (normalizer_le_normalizer_pCoreOf 2 _)
  have hPQ : pCoreOf 2 (Subgroup.centralizer (E : Set G)) ≤ QE153 E :=
    le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 _).trans hCN) hCC (pCoreOf_isPGroup 2 _)
  exact fun x hx => QE_le_K167 h113 k (hPQ (hPC hx))

theorem commutator_tau_CE_le_K167 (h113 : StageLemma14113) (k : Ctx67 G T Mc M V₁ V₂ E t) {τ c : G}
    (hτQ : τ ∈ pCoreOf 2 Mc) (hτTE : τ ∈ TE153 T E) (hc : c ∈ Subgroup.centralizer (E : Set G)) :
    τ * c * τ⁻¹ * c⁻¹ ∈ K167 T M E := by
  have hCM : Subgroup.centralizer (E : Set G) ≤ Mc := k.r66.centralizer_le_mc
  have hτN : τ ∈ Subgroup.normalizer (E : Set G) := hτTE.2
  refine pCoreOf_Mc_inf_CE_le_K167 h113 k ⟨?_, ?_⟩
  · have h1 : c * τ⁻¹ * c⁻¹ ∈ pCoreOf 2 Mc :=
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 Mc (hCM hc)) τ⁻¹).mp
        ((pCoreOf 2 Mc).inv_mem hτQ)
    have := (pCoreOf 2 Mc).mul_mem hτQ h1
    simpa [mul_assoc] using this
  · have h1 : τ * c * τ⁻¹ ∈ Subgroup.centralizer (E : Set G) :=
      (Subgroup.mem_normalizer_iff.mp (normalizer_le_normalizer_CE E hτN) c).mp hc
    exact (Subgroup.centralizer (E : Set G)).mul_mem h1 ((Subgroup.centralizer _).inv_mem hc)

theorem mul_self_tau_mem_K167 (h113 : StageLemma14113) (k : Ctx67 G T Mc M V₁ V₂ E t) {τ : G}
    (hτQ : τ ∈ pCoreOf 2 Mc) (hττ : τ * τ ∈ Subgroup.centralizer (VZ T M : Set G)) :
    τ * τ ∈ K167 T M E :=
  pCoreOf_Mc_inf_CE_le_K167 h113 k ⟨(pCoreOf 2 Mc).mul_mem hτQ hτQ,
    Subgroup.centralizer_le k.L.le_V hττ⟩

end O2

end S1567

end CFSG.Quasithin
