module

public import CFSG.Quasithin.Background.G64RealizeSec
public import CFSG.Quasithin.Background.B5FinSp
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.Quasithin.H13.Ch3Sec3

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped commutatorElement

section Transfer

variable {V : Type} [CommGroup V]

theorem realizesVia_sup_of_inf {D : FFModel} {H : Subgroup (MulAut V)} {U C : Subgroup V}
    {π : D.Gam →* ↥H} (hC : ∀ h : ↥H, ∀ c ∈ C, (h : MulAut V) c ∈ C)
    (h : D.RealizesVia H U (U ⊓ C) π) : D.RealizesVia H (U ⊔ C) C π := by
  obtain ⟨hπ, -, hks, hU, -, hsec, hker, β, hβs, hβk, hβe⟩ := h
  set e := QuotientGroup.quotientInfEquivProdNormalQuotient U C with he
  have hβC : C.subgroupOf U ≤ β.ker := fun u hu =>
    MonoidHom.mem_ker.mpr ((hβk u).mpr ⟨u.2, Subgroup.mem_subgroupOf.mp hu⟩)
  set βbar := QuotientGroup.lift (C.subgroupOf U) β hβC with hβbar
  set β' : ↥(U ⊔ C) →* ↥D.sec ⧸ D.ker.subgroupOf D.sec :=
    βbar.comp (e.symm.toMonoidHom.comp (QuotientGroup.mk' (C.subgroupOf (U ⊔ C)))) with hβ'
  have key : ∀ (w : ↥(U ⊔ C)) (u : ↥U) (c : V), c ∈ C → (w : V) = u * c → β' w = β u := by
    intro w u c hc hw
    have h1 : QuotientGroup.mk' (C.subgroupOf (U ⊔ C)) w =
        QuotientGroup.mk' (C.subgroupOf (U ⊔ C)) (Subgroup.inclusion le_sup_left u) := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
        Subgroup.mem_subgroupOf]
      have e1 : (((w⁻¹ * Subgroup.inclusion le_sup_left u : ↥(U ⊔ C)) : V)) = c⁻¹ := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inclusion, hw]
        group
      rw [e1]
      exact C.inv_mem hc
    have h2 : e (QuotientGroup.mk u) =
        QuotientGroup.mk' (C.subgroupOf (U ⊔ C)) (Subgroup.inclusion le_sup_left u) := rfl
    rw [hβ', MonoidHom.comp_apply, MonoidHom.comp_apply, h1, ← h2, MulEquiv.coe_toMonoidHom,
      MulEquiv.symm_apply_apply, hβbar, QuotientGroup.lift_mk]
  have hdec : ∀ w : ↥(U ⊔ C), ∃ u : ↥U, ∃ c ∈ C, (w : V) = u * c := by
    intro w
    obtain ⟨u, hu, c, hc, huc⟩ := Subgroup.mem_sup.mp w.2
    exact ⟨⟨u, hu⟩, c, hc, huc.symm⟩
  refine ⟨hπ, le_sup_right, hks, fun g w hw => ?_, hC, hsec, hker, β', ?_, fun w => ?_, ?_⟩
  · obtain ⟨u, hu, c, hc, rfl⟩ := Subgroup.mem_sup.mp hw
    rw [map_mul]
    exact Subgroup.mul_mem_sup (hU g u hu) (hC g c hc)
  · intro q
    obtain ⟨u, rfl⟩ := hβs q
    exact ⟨Subgroup.inclusion le_sup_left u, key _ u 1 C.one_mem (by simp)⟩
  · obtain ⟨u, c, hc, hw⟩ := hdec w
    rw [key w u c hc hw, hβk u]
    constructor
    · rintro ⟨-, huC⟩
      rw [hw]
      exact C.mul_mem huC hc
    · intro hwC
      refine ⟨u.2, ?_⟩
      have : (u : V) = w * c⁻¹ := by rw [hw]; group
      rw [this]
      exact C.mul_mem hwC (C.inv_mem hc)
  · intro γ w m hw' hm hwm
    obtain ⟨u, c, hc, hw⟩ := hdec w
    rw [key w u c hc hw] at hwm
    have hu' : ((π γ : ↥H) : MulAut V) (u : V) ∈ U := hU (π γ) u u.2
    refine (key ⟨_, hw'⟩ ⟨_, hu'⟩ (((π γ : ↥H) : MulAut V) c) (hC (π γ) c hc) ?_).trans
      (hβe γ u m hu' hm hwm)
    simp only [hw, map_mul]

theorem realizes_sup_of_inf {D : FFModel} {H : Subgroup (MulAut V)} {U C : Subgroup V}
    (hC : ∀ h : ↥H, ∀ c ∈ C, (h : MulAut V) c ∈ C) (h : D.Realizes H U (U ⊓ C)) :
    D.Realizes H (U ⊔ C) C := by
  obtain ⟨π, hπ⟩ := h
  exact ⟨π, realizesVia_sup_of_inf hC hπ⟩

theorem directSumOfCopies_sup {H : Subgroup (MulAut V)} {U C : Subgroup V} {D : FFModel} {k : ℕ}
    (hC : ∀ h : ↥H, ∀ c ∈ C, (h : MulAut V) c ∈ C) (hUC : U ⊓ C = ⊥)
    (h : DirectSumOfCopies H U ⊥ D k) : DirectSumOfCopies H (U ⊔ C) C D k := by
  obtain ⟨I, π, -, hind, hsup, hreal⟩ := h
  have hIU : ∀ i, I i ≤ U := fun i => by
    rw [← hsup]
    exact le_sup_of_le_right (le_iSup I i)
  refine ⟨fun i => I i ⊔ C, π, fun i => le_sup_right, fun i => ?_, ?_, fun i => ?_⟩
  · refine le_antisymm (fun x hx => ?_) (le_inf le_sup_right le_sup_left)
    obtain ⟨hx₁, hx₂⟩ := hx
    obtain ⟨a, ha, c₁, hc₁, rfl⟩ := Subgroup.mem_sup.mp hx₁
    have hle : C ⊔ ⨆ (j : Fin k) (_ : j ≠ i), I j ⊔ C ≤ C ⊔ ⨆ (j : Fin k) (_ : j ≠ i), I j := by
      refine sup_le le_sup_left (iSup₂_le fun j hj => sup_le ?_ le_sup_left)
      exact le_sup_of_le_right (le_iSup₂_of_le j hj le_rfl)
    obtain ⟨c₂, hc₂, b, hb, hcb⟩ := Subgroup.mem_sup.mp (hle hx₂)
    have hbU : b ∈ U := by
      have : (⨆ (j : Fin k) (_ : j ≠ i), I j) ≤ U := iSup₂_le fun j _ => hIU j
      exact this hb
    have hab : a * b⁻¹ ∈ U ⊓ C := by
      refine ⟨U.mul_mem (hIU i ha) (U.inv_mem hbU), ?_⟩
      have : a * b⁻¹ = c₂ * c₁⁻¹ := by
        have e : a * c₁ = c₂ * b := hcb.symm
        have ha : a = c₂ * b * c₁⁻¹ := by rw [← e]; group
        calc a * b⁻¹ = c₂ * (b * c₁⁻¹ * b⁻¹) := by rw [ha]; group
          _ = c₂ * c₁⁻¹ := by rw [mul_comm b c₁⁻¹, mul_assoc, mul_inv_cancel, mul_one]
      rw [this]
      exact C.mul_mem hc₂ (C.inv_mem hc₁)
    rw [hUC, Subgroup.mem_bot] at hab
    have hab' : a = b := by
      have := congrArg (· * b) hab
      simpa using this
    have ha1 : a ∈ I i ⊓ (⊥ ⊔ ⨆ (j : Fin k) (_ : j ≠ i), I j) :=
      ⟨ha, by rw [bot_sup_eq, hab']; exact hb⟩
    rw [hind i, Subgroup.mem_bot] at ha1
    rw [ha1, one_mul]
    exact hc₁
  · refine le_antisymm (sup_le le_sup_right (iSup_le fun i => sup_le ?_ le_sup_right)) ?_
    · exact le_sup_of_le_left (hIU i)
    · refine sup_le ?_ le_sup_left
      rw [← hsup, bot_sup_eq]
      exact iSup_le fun i => le_sup_of_le_right (le_iSup_of_le i le_sup_left)
  · have h1 : I i ⊓ C = ⊥ := le_bot_iff.mp (hUC ▸ inf_le_inf_right C (hIU i))
    have := hreal i
    rw [← h1] at this
    exact realizesVia_sup_of_inf hC this

end Transfer

section Ident

variable {V : Type} [CommGroup V]

theorem nonempty_mulEquiv_of_realizes {D : FFModel} (hD : D.Faithful) {H : Subgroup (MulAut V)}
    {U Z : Subgroup V} (h : D.Realizes H U Z) : Nonempty (↥H ≃* D.Gam) := by
  obtain ⟨π, hπ⟩ := h
  exact ⟨(MulEquiv.ofBijective π ⟨G64.RealizesVia.injective_of_faithful' hD hπ, hπ.1⟩).symm⟩

theorem not_isPerfect_perm_six : ¬ Group.IsPerfect (Equiv.Perm (Fin 6)) := by
  intro hp
  have hle : commutator (Equiv.Perm (Fin 6)) ≤
      (Equiv.Perm.sign : Equiv.Perm (Fin 6) →* ℤˣ).ker := by
    rw [commutator_def, Subgroup.commutator_le]
    intro g _ h _
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm, mul_comm]
  rw [Group.isPerfect_def.mp hp] at hle
  have h1 := hle (Subgroup.mem_top (Equiv.swap (0 : Fin 6) 1))
  rw [MonoidHom.mem_ker, Equiv.Perm.sign_swap (by decide)] at h1
  exact absurd h1 (by decide)

theorem not_isPerfect_statedSp_two {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) :
    ¬ Group.IsPerfect ↥(CFSG.Assembly.LowTwoRank.StatedSp 2 K) := by
  intro hp
  have : Fintype K := Fintype.ofFinite K
  have hF : Fintype.card K = 2 := by rw [← Nat.card_eq_fintype_card, hK]
  let c : ZMod 2 ≃+* K := ZMod.ringEquivOfPrime K Nat.prime_two hF
  apply not_isPerfect_perm_six
  exact Group.IsPerfect.ofSurjective
    (f := ((CFSG.Quasithin.B5FinSp.theta c).symm :
      ↥(CFSG.Assembly.LowTwoRank.StatedSp 2 K) →* Equiv.Perm (Fin 6)))
    (CFSG.Quasithin.B5FinSp.theta c).symm.surjective

end Ident

end CFSG.Quasithin.H13.Ch3Sec3
