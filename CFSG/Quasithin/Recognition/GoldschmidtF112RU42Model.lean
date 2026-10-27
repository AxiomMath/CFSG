module

public import CFSG.Quasithin.Recognition.GoldschmidtF112RU42Mc
public import CFSG.GH74.QTGen4.U42.ModelU
public import CFSG.GH74.QTGen4.U42.ModelCoordsRelabelled
public import CFSG.Quasithin.Recognition.F112RShapes

public section

namespace CFSG.Quasithin.F112R.U42M

open CFSG.Open CFSG.GH74.QTGen4.U42 CFSG.Quasithin.A5Model CFSG.Quasithin.H13.A5
open CFSG.Quasithin.H13.F431.U42 U42F431

theorem exists_embedding_P2 :
    ∃ f : ↥P2 →* Mc, Function.Injective f ∧ f.range = Mof (alternatingGroup (Fin 5)) ∧
      (∀ g : ↥P2, (g : Y) ∈ pCoreOf 2 P1 ↔ f g ∈ U0) ∧
      ∀ w : W5, ∃ v ∈ Vsub, ∃ hv : v ∈ P2, f ⟨v, hv⟩ = SemidirectProduct.inl w := by
  obtain ⟨e, he1, he2⟩ := exists_model_coords_relabelled
  refine ⟨(Mof (alternatingGroup (Fin 5))).subtype.comp e.toMonoidHom,
    Subtype.coe_injective.comp e.injective, ?_, fun g => model_U_iff e he1 he2 g, ?_⟩
  · rw [MonoidHom.range_comp, MonoidHom.range_eq_top.2 e.surjective, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  · intro w
    obtain ⟨v, hv⟩ := psiEq.surjective ((pact sigma0)⁻¹ w)
    refine ⟨(v : Y), v.2, Vsub_le_P2 v.2, ?_⟩
    change ((e ⟨(v : Y), Vsub_le_P2 v.2⟩ : Mof _) : Mc) = _
    rw [he1 (v : Y) v.2]
    congr 1
    rw [show (⟨(v : Y), v.2⟩ : ↥Vsub) = v from rfl, hv]
    simp

theorem perfect_P2 : ⁅P2, P2⁆ = P2 := by
  obtain ⟨f, hf, hr, -, -⟩ := exists_embedding_P2
  have htop : ⁅(⊤ : Subgroup ↥P2), (⊤ : Subgroup ↥P2)⁆ = (⊤ : Subgroup ↥P2) := by
    apply Subgroup.map_injective hf
    rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, hr, perfect_Mof]
  have h := congrArg (Subgroup.map P2.subtype) htop
  rwa [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at h

theorem eq_one_of_central_P2 {g : Y} (hg : g ∈ P2) (h : ∀ k ∈ P2, g * k = k * g) : g = 1 := by
  obtain ⟨f, hf, hr, -, -⟩ := exists_embedding_P2
  have h1 : f ⟨g, hg⟩ = 1 := by
    apply eq_one_of_central_Mof
    intro y hy
    rw [← hr] at hy
    obtain ⟨k, rfl⟩ := hy
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (h k k.2)
  have := hf (h1.trans (map_one f).symm)
  exact congrArg Subtype.val this

theorem exists_three_fix_P2 :
    ∃ x ∈ P2, orderOf x = 3 ∧ ∃ v ∈ Vsub, v ≠ 1 ∧ v * x = x * v := by
  obtain ⟨f, hf, hr, -, hV⟩ := exists_embedding_P2
  have hx : (SemidirectProduct.inr c3 : Mc) ∈ f.range := hr ▸ mem_Mof.2 (by simpa using c3_mem)
  obtain ⟨x, hx⟩ := hx
  obtain ⟨v, hvV, hvP, hv⟩ := hV w34
  refine ⟨x, x.2, ?_, v, hvV, ?_, ?_⟩
  · rw [orderOf_submonoid, ← orderOf_injective f hf, hx, orderOf_c3]
  · intro h1
    apply w34_ne_one
    have h2 : (SemidirectProduct.inl w34 : Mc) = 1 := by
      rw [← hv]
      have : (⟨v, hvP⟩ : ↥P2) = 1 := Subtype.ext h1
      rw [this, map_one]
    simpa using congrArg SemidirectProduct.left h2
  · have := comm_w34_c3
    rw [← hv, ← hx, ← map_mul, ← map_mul] at this
    exact congrArg Subtype.val (hf this)

theorem inK4_mem_alternating : ∀ σ : Equiv.Perm (Fin 5), InK4 σ → σ ∈ alternatingGroup (Fin 5) := by
  rintro σ (rfl | rfl | rfl | rfl) <;> rw [Equiv.Perm.mem_alternatingGroup] <;> decide

theorem isSpecialPow_pCoreOf_P1 : CFSG.Quasithin.IsSpecialPow 2 2 2 ↥(pCoreOf 2 P1) := by
  obtain ⟨f, hf, hr, hU, -⟩ := exists_embedding_P2
  set R := pCoreOf 2 P1
  have hSyl : CFSG.QuasithinUnique.IsSylowTwoOf T P1 :=
    ⟨T_le_B0.trans B0_le_P1, isSylow_T.2.1, by
      show ¬ 2 ∣ T.relIndex P1
      have h := Subgroup.relIndex_mul_card (H := T) (K := P1)
      rw [inf_eq_left.mpr (T_le_B0.trans B0_le_P1), card_T, card_P1] at h
      have : T.relIndex P1 = 9 := by omega
      rw [this]
      norm_num⟩
  have hRP2 : R ≤ P2 := (CFSG.Quasithin.F7.isSylowTwoOf_pCoreOf_le hSyl).trans T_le_P2'
  have hX : (R.subgroupOf P2).map f = U0 := by
    ext x
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact (hU a).1 (Subgroup.mem_subgroupOf.1 ha)
    · intro hx
      have hxr : x ∈ f.range := hr ▸ mem_Mof.2 (inK4_mem_alternating _ hx.2)
      obtain ⟨a, rfl⟩ := hxr
      exact ⟨a, Subgroup.mem_subgroupOf.2 ((hU a).2 hx), rfl⟩
  let e : ↥R ≃* ↥U0 := (Subgroup.subgroupOfEquivOfLe hRP2).symm.trans
    (((R.subgroupOf P2).equivMapOfInjective f hf).trans (MulEquiv.subgroupCongr hX))
  exact CFSG.Quasithin.IsSpecialPow.of_mulEquiv e.symm isSpecialPow_U0

end CFSG.Quasithin.F112R.U42M
