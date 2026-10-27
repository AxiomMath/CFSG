module

public import CFSG.Quasithin.Vol2.Ch10SecB3L32

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.ComponentClassification

namespace L32

theorem slConjugation_eq_conj (A : GL (Fin 3) (ZMod 2)) :
    CatalogueBHigherLinearAction.slConjugation 3 (ZMod 2) A =
      MulAut.conj ((QuasithinUnique.Setup.Family.slEquivGL 3).symm A) := by
  ext g : 1
  apply Matrix.SpecialLinearGroup.toGL_injective
  have hA : Matrix.SpecialLinearGroup.toGL ((QuasithinUnique.Setup.Family.slEquivGL 3).symm A) =
      A := (QuasithinUnique.Setup.Family.slEquivGL 3).apply_symm_apply A
  rw [CatalogueBHigherLinearAction.toGL_slConjugation, MulAut.conj_apply, map_mul, map_mul,
    map_inv, hA]

theorem aut_cases (α : MulAut Γ) : (∃ g : Γ, α = MulAut.conj g) ∨
    ∃ g : Γ, α = MulAut.conj g * CatalogueBGraphForm.slGraphAut 3 (ZMod 2) := by
  rcases QuasithinUnique.Setup.Family.aut_SL3_cases α with ⟨A, hA⟩ | ⟨A, hA⟩
  · exact Or.inl ⟨_, hA.trans (slConjugation_eq_conj A)⟩
  · exact Or.inr ⟨_, hA.trans (by rw [slConjugation_eq_conj])⟩

theorem graph_not_pa : ∀ g : Γ,
    (∀ u ∈ uList, IsU (g * CatalogueBGraphForm.slGraphAut 3 (ZMod 2) u * g⁻¹)) →
      ¬ IsPa (g * CatalogueBGraphForm.slGraphAut 3 (ZMod 2) s1 * g⁻¹) := by
  unfold uList IsU IsPa ent; decide +kernel

theorem graph_not_pb : ∀ g : Γ,
    (∀ u ∈ uList, IsU (g * CatalogueBGraphForm.slGraphAut 3 (ZMod 2) u * g⁻¹)) →
      ¬ IsPb (g * CatalogueBGraphForm.slGraphAut 3 (ZMod 2) s2 * g⁻¹) := by
  unfold uList IsU IsPb ent; decide +kernel

theorem eq_conj_of_normalizes {β : MulAut Γ} (hU : ∀ u ∈ U3, β u ∈ U3) {A : Subgroup Γ}
    (hA : A = Pa ∨ A = Pb) (hβA : ∀ a ∈ A, β a ∈ A) :
    ∃ u : Γ, IsU u ∧ ∀ g, β g = u * g * u⁻¹ := by
  rcases aut_cases β with ⟨g, rfl⟩ | ⟨g, rfl⟩
  · exact ⟨g, normalizer_U3_aux g fun u hu => hU u ((mem_uList_iff u).mp hu),
      fun x => MulAut.conj_apply g x⟩
  · exfalso
    have hU' : ∀ u ∈ uList, IsU (g * CatalogueBGraphForm.slGraphAut 3 (ZMod 2) u * g⁻¹) :=
      fun u hu => hU u ((mem_uList_iff u).mp hu)
    rcases hA with rfl | rfl
    · exact graph_not_pa g hU' (hβA s1 s_mem.1)
    · exact graph_not_pb g hU' (hβA s2 s_mem.2.2.1)

end L32

variable {G : Type} [Group G]

theorem isXSectionIso_of_equiv {X A B : Subgroup G} (e : ↥A ≃* ↥B)
    (he : ∀ x ∈ X, ∀ (a : ↥A) (ha : x * (a : G) * x⁻¹ ∈ A),
      ((e ⟨x * (a : G) * x⁻¹, ha⟩ : ↥B) : G) = x * (e a : G) * x⁻¹) :
    IsXSectionIso X ⊥ A B := by
  have hnA : ((⊥ : Subgroup G).subgroupOf A).Normal := by
    rw [Subgroup.bot_subgroupOf]; infer_instance
  have hnB : ((⊥ : Subgroup G).subgroupOf B).Normal := by
    rw [Subgroup.bot_subgroupOf]; infer_instance
  obtain ⟨qA, hqA⟩ : ∃ q : ↥A ⧸ (⊥ : Subgroup G).subgroupOf A ≃* ↥A,
      ∀ a : ↥A, q (a : ↥A ⧸ (⊥ : Subgroup G).subgroupOf A) = a :=
    ⟨(QuotientGroup.quotientMulEquivOfEq (Subgroup.bot_subgroupOf A)).trans
      QuotientGroup.quotientBot, fun _ => rfl⟩
  obtain ⟨qB, hqB⟩ : ∃ q : ↥B ⧸ (⊥ : Subgroup G).subgroupOf B ≃* ↥B,
      ∀ b : ↥B, q (b : ↥B ⧸ (⊥ : Subgroup G).subgroupOf B) = b :=
    ⟨(QuotientGroup.quotientMulEquivOfEq (Subgroup.bot_subgroupOf B)).trans
      QuotientGroup.quotientBot, fun _ => rfl⟩
  refine ⟨hnA, hnB, (qA.trans e).trans qB.symm, ?_⟩
  intro x hx j k hj hk hjk
  have h1 : e j = k := by
    have := congrArg qB hjk
    rwa [MulEquiv.trans_apply, MulEquiv.trans_apply, MulEquiv.apply_symm_apply, hqA, hqB] at this
  apply qB.injective
  rw [MulEquiv.trans_apply, MulEquiv.trans_apply, MulEquiv.apply_symm_apply, hqA, hqB]
  apply Subtype.ext
  rw [he x hx j hj, h1]

theorem isXSectionIso_of_inner {L W : Subgroup G} {s x₀ : G} (hx₀ : x₀ ∈ L)
    (hLW : L ≤ Subgroup.normalizer (W : Set G))
    (hO : pCoreOf 2 L ≤ Subgroup.centralizer (W : Set G))
    (hinner : ∀ x ∈ L, s * x * s⁻¹ * (x₀ * x * x₀⁻¹)⁻¹ ∈ pCoreOf 2 L) :
    IsXSectionIso L ⊥ W (CFSG.conjugate W s) := by
  set e : ↥W ≃* ↥(CFSG.conjugate W s) := (conjAct W ⟨x₀, hLW hx₀⟩).trans (conjEquiv W s)
  have he : ∀ a : ↥W, ((e a : ↥(CFSG.conjugate W s)) : G) = s⁻¹ * (x₀ * a * x₀⁻¹) * s :=
    fun a => by rw [MulEquiv.trans_apply, conjEquiv_coe, conjAct_apply_coe]
  refine isXSectionIso_of_equiv e fun x hx a ha => ?_
  rw [he, he]
  set o := s * x * s⁻¹ * (x₀ * x * x₀⁻¹)⁻¹ with ho
  set w := x₀ * (x * (a : G) * x⁻¹) * x₀⁻¹ with hw
  have hwW : w ∈ W := (Subgroup.mem_normalizer_iff.mp (hLW hx₀) _).mp ha
  have hco : w * o = o * w := Subgroup.mem_centralizer_iff.mp (hO (hinner x hx)) w hwW
  have h1 : x * (s⁻¹ * (x₀ * (a : G) * x₀⁻¹) * s) * x⁻¹ = s⁻¹ * (o * w * o⁻¹) * s := by
    rw [ho, hw]; group
  have h2 : o * w * o⁻¹ = w := by rw [← hco]; group
  rw [h1, h2, hw]

variable [Finite G] {T L I : Subgroup G}

namespace Ctx3

variable {H B : Subgroup G} {t : G} {Ψ : ↥(fsuL0 T L) →* L32.Γ × L32.Γ} {α : MulAut L32.Γ}
  {ψ : (↥L ⧸ CFSG.pCore 2 ↥L) ≃* L32.Γ}

theorem not_case_five (c : Ctx3 T L I H B t Ψ α ψ) (hB1 : B ≠ ⊥) (h5 : Case10_1_1Five T L I) :
    False := by
  obtain ⟨-, s, hsT, hsN, W, hWU, hLW, -, -, -, hnot⟩ := h5
  obtain ⟨A, hA, hY, -⟩ := c.classify' hB1
  have hmem : ∀ (l : G) (hl : l ∈ L),
      l ∈ (H ⊓ fsuM T L) ⊓ fsuL0 T L ↔ ψ (mkO2 L l hl) ∈ A := by
    intro l hl
    rw [hY, mem_preIn]
    constructor
    · rintro ⟨hl0, h⟩
      rw [c.hC.onL l hl0 hl] at h
      exact h.1
    · intro h
      refine ⟨SecA.le_fsuL0 T L hl, ?_⟩
      rw [c.hC.onL l _ hl]
      exact ⟨h, A.one_mem⟩
  have hsurj : ∀ g : L32.Γ, ∃ (l : G) (hl : l ∈ L), ψ (mkO2 L l hl) = g := by
    intro g
    obtain ⟨⟨l, hl⟩, hq⟩ := QuotientGroup.mk_surjective (ψ.symm g)
    exact ⟨l, hl, by rw [mkO2, hq, MulEquiv.apply_symm_apply]⟩
  set β := autCoord ψ hsN with hβ
  have hsX : s ∈ H ⊓ fsuM T L := ⟨c.hH.1.1 hsT, SecA.le_fsuM T L hsT⟩
  have hU : ∀ u ∈ L32.U3, β u ∈ L32.U3 := by
    intro u hu
    rw [← c.hC.hψ] at hu ⊢
    obtain ⟨_, ⟨⟨d, hdL⟩, hdT, rfl⟩, rfl⟩ := hu
    have hdT' : d ∈ T ⊓ L := Subgroup.mem_subgroupOf.mp hdT
    have hsd : s * d * s⁻¹ ∈ T ⊓ L :=
      ⟨T.mul_mem (T.mul_mem hsT hdT'.1) (T.inv_mem hsT),
        (Subgroup.mem_normalizer_iff.mp hsN d).mp hdL⟩
    refine ⟨_, ⟨⟨s * d * s⁻¹, hsd.2⟩, Subgroup.mem_subgroupOf.mpr hsd, rfl⟩, ?_⟩
    exact autCoord_apply ψ hsN hdL hsd.2
  have hβA : ∀ a ∈ A, β a ∈ A := by
    intro a ha
    obtain ⟨l, hl, rfl⟩ := hsurj a
    have hlY := (hmem l hl).mpr ha
    have hsl : s * l * s⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp hsN l).mp hl
    have hslY : s * l * s⁻¹ ∈ (H ⊓ fsuM T L) ⊓ fsuL0 T L :=
      ⟨(H ⊓ fsuM T L).mul_mem ((H ⊓ fsuM T L).mul_mem hsX hlY.1) ((H ⊓ fsuM T L).inv_mem hsX),
        (Subgroup.mem_normalizer_iff.mp hsX.2 l).mp hlY.2⟩
    rw [← autCoord_apply ψ hsN hl hsl]
    exact (hmem _ hsl).mp hslY
  obtain ⟨u, -, hβu⟩ := L32.eq_conj_of_normalizes hU hA hβA
  obtain ⟨x₀, hx₀, hx₀u⟩ := hsurj u
  have hinner : ∀ x ∈ L, s * x * s⁻¹ * (x₀ * x * x₀⁻¹)⁻¹ ∈ pCoreOf 2 L := by
    intro x hx
    have hsx := (Subgroup.mem_normalizer_iff.mp hsN x).mp hx
    have hm : x₀ * x * x₀⁻¹ ∈ L := L.mul_mem (L.mul_mem hx₀ hx) (L.inv_mem hx₀)
    rw [← mk_eq_mk_iff hsx hm]
    apply ψ.injective
    rw [autCoord_apply ψ hsN hx hsx, hβu, ← hx₀u, ← map_inv, ← map_mul, ← map_mul, ← mkO2_inv,
      ← mkO2_mul, ← mkO2_mul]
  have hO : pCoreOf 2 L ≤ Subgroup.centralizer (W : Set G) :=
    (SecA.pCoreOf_le_centralizer_fsuVM c.h322 c.hyp).trans
      (Subgroup.centralizer_le (hWU.trans (fsuUL_le' T L I)))
  exact hnot (isXSectionIso_of_inner hx₀ hLW hO hinner)

end Ctx3

end CFSG.Quasithin.Vol2.Ch10.SecB
