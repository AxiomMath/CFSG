module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKK1IIISpSiegel
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2ShortSp
public import CFSG.LocalAnalysis.StandardType.GGSixRCKK1IIISpPairAux
public import CFSG.GH74.GLS.Bg.TwoGroups.Lemma21c
public import CFSG.HardMathSupport.Curtis.Coordinator.PerfThreeOrthPieces
public import CFSG.Quasithin.EmptyFaithful.S146zRSLB
public import TauCeti.Algebra.Group.Subgroup.ZPowers
public import CFSG.Quasithin.Vol2.KGFactC31RuRef
public import CFSG.GH74.GLS.Bg.TwoGroups.Lemma21a

public section

namespace CFSG.StandardType.RCKK1IIISp

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.StandardType
  CFSG.StandardType.RCKC1 CFSG.Open
open CFSG.LieType.BorelTits CFSG.StandardType.LieKnownR2.Short CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher CFSG.QuasithinUnique.B113Lie.Sp
open scoped Matrix commutatorElement

theorem rckSp_pair {m : ℕ} (hm : 3 ≤ m)
    {β : Fin (Symplectic.rootDatum m (GaloisField 2 1)).rank → ℤ}
    (hβ : β ∈ (Symplectic.rootDatum m (GaloisField 2 1)).roots)
    (hs : ¬ GGLongRoot (Symplectic.rootDatum m (GaloisField 2 1)) β) :
    ∃ (r : ↥(StatedSp m (GaloisField 2 1))) (V : Subgroup ↥(StatedSp m (GaloisField 2 1))),
      r ∈ (Symplectic.rootDatum m (GaloisField 2 1)).rootGroup β ∧ r ≠ 1 ∧ r ∈ V ∧
      IsElemAbelian 2 V ∧ Nat.card V = 4 ∧
      (∀ v ∈ V, v ≠ 1 → ∃ j : ↥(StatedSp m (GaloisField 2 1)), v = j * r * j⁻¹) ∧
      ∀ y ∈ pCoreOf 2 (Subgroup.centralizer ({r} : Set ↥(StatedSp m (GaloisField 2 1)))),
        ∀ v ∈ V, y * v * y⁻¹ * v⁻¹ ∈ Subgroup.zpowers r := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hgf2 : ∀ x : GaloisField 2 1, x = 0 ∨ x = 1 := fun x =>
    CFSG.HardMathSupport.Curtis.Coordinator.eq_zero_or_one_of_card_two
      (by simpa using CFSG.LieType.Catalog.card_galoisField 2 1 (by norm_num)) x
  let F := GaloisField 2 1
  let G := ↥(StatedSp m F)
  let VV := Fin m ⊕ Fin m → F
  obtain ⟨a₁, a₂, b₁, b₂, h1, h2, ⟨h3, h4, h5, h6⟩, hA, _hB⟩ :=
    CFSG.StandardType.LieKnownR2.Geo.exists_altSiegelGroup_eq_conj_rootGroup_Sp m F hβ hs 1
  set A : Submodule F VV := Submodule.span F {a₁, a₂} with hAdef
  have s1 : a₁ ⬝ᵥ (spJ m F *ᵥ a₁) = 0 := spForm_self m F a₁
  have s2 : a₂ ⬝ᵥ (spJ m F *ᵥ a₂) = 0 := spForm_self m F a₂
  have s12 : a₁ ⬝ᵥ (spJ m F *ᵥ a₂) = 0 := h3
  have s21 : a₂ ⬝ᵥ (spJ m F *ᵥ a₁) = 0 := (spForm m F).refl a₁ a₂ s12
  have hW : (spForm m F).IsTotallyIsotropic A := by
    intro x hx y hy
    obtain ⟨c₁, c₂, rfl⟩ := Submodule.mem_span_pair.mp hx
    obtain ⟨d₁, d₂, rfl⟩ := Submodule.mem_span_pair.mp hy
    simp only [spForm_β, Matrix.mulVec_add, Matrix.mulVec_smul, add_dotProduct, dotProduct_add,
      smul_dotProduct, dotProduct_smul, smul_eq_mul, s1, s2, s12, s21]
    ring
  have hroot : (Symplectic.rootDatum m F).rootGroup β = spAltSiegel m F a₁ a₂ := by
    have hconj : Subgroup.map (MulAut.conj (1 : G)).toMonoidHom
        ((Symplectic.rootDatum m F).rootGroup β) = (Symplectic.rootDatum m F).rootGroup β := by
      rw [show (MulAut.conj (1 : G)).toMonoidHom = MonoidHom.id G from by
        ext x; simp [MulAut.conj], Subgroup.map_id]
    rw [← hconj, ← Subgroup.comap_map_eq_self_of_injective (StatedSp m F).subtype_injective
      (Subgroup.map (MulAut.conj (1 : G)).toMonoidHom ((Symplectic.rootDatum m F).rootGroup β)),
      hA]
    rfl
  have ha1ne : a₁ ≠ 0 := by
    intro h0; rw [h0] at h1; simp at h1
  have ha2ne : a₂ ≠ 0 := by
    intro h0; rw [h0] at h2; simp at h2
  have ha12ne : a₁ ≠ a₂ := by
    intro h; rw [h, h6] at h1; exact zero_ne_one h1
  have hli : LinearIndependent F ![a₁, a₂] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    constructor
    · have h := congrArg (fun x => x ⬝ᵥ (spJ m F *ᵥ b₁)) hst
      simp only [add_dotProduct, smul_dotProduct, smul_eq_mul] at h
      rw [show a₁ ⬝ᵥ (spJ m F *ᵥ b₁) = 1 from h1,
        show a₂ ⬝ᵥ (spJ m F *ᵥ b₁) = 0 from h6,
        mul_one, mul_zero, add_zero, zero_dotProduct] at h
      exact h
    · have h := congrArg (fun x => x ⬝ᵥ (spJ m F *ᵥ b₂)) hst
      simp only [add_dotProduct, smul_dotProduct, smul_eq_mul] at h
      rw [show a₁ ⬝ᵥ (spJ m F *ᵥ b₂) = 0 from h5,
        show a₂ ⬝ᵥ (spJ m F *ᵥ b₂) = 1 from h2,
        mul_zero, mul_one, zero_add, zero_dotProduct] at h
      exact h
  have hfinA : Module.finrank F A = 2 := by
    have hrange : Set.range ![a₁, a₂] = ({a₁, a₂} : Set VV) := by
      ext x; constructor
      · rintro ⟨i, rfl⟩; fin_cases i <;> simp
      · rintro (rfl | rfl)
        · exact ⟨0, rfl⟩
        · exact ⟨1, rfl⟩
    rw [hAdef, ← hrange, finrank_span_eq_card hli]
    simp
  have hfin_perp : Module.finrank F ((spForm m F).perp A) = 2 * m - 2 := by
    have h := (spForm m F).finrank_perp A
    have hV : Module.finrank F VV = 2 * m := by
      rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]; ring
    rw [hfinA, hV] at h
    omega
  have hlt : A < (spForm m F).perp A :=
    Submodule.lt_of_le_of_finrank_lt_finrank hW (by rw [hfinA, hfin_perp]; omega)
  obtain ⟨c, hc_perp, hcA⟩ := (SetLike.lt_iff_le_and_exists.mp hlt).2
  have hcne : c ≠ 0 := fun h0 => hcA (by rw [h0]; exact A.zero_mem)
  have hB1c : spB m a₁ c = 0 :=
    ((spForm m F).mem_perp.mp hc_perp) a₁ (Submodule.subset_span (by simp))
  have hB2c : spB m a₂ c = 0 :=
    ((spForm m F).mem_perp.mp hc_perp) a₂ (Submodule.subset_span (by simp))
  have hBc1 : spB m c a₁ = 0 := (spForm m F).refl a₁ c hB1c
  have hBc2 : spB m c a₂ = 0 := (spForm m F).refl a₂ c hB2c
  have hB12 : spB m a₁ a₂ = 0 := h3
  obtain ⟨r, hr⟩ := spSiegel_exists (m := m) (x := a₁) (y := a₂) hB12
  have hr_mem : r ∈ spAltSiegel m F a₁ a₂ := by
    refine mem_spAltSiegel_of_mulVec (1 : F) (fun v => ?_)
    have hv : ((r : GL (Fin m ⊕ Fin m) F) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) F) *ᵥ v =
        v + spB m a₂ v • a₁ + spB m a₁ v • a₂ := hr v
    rw [hv]
    simp only [one_mul, spB_eq_spForm, spForm_β]
  have hr_root : r ∈ (Symplectic.rootDatum m F).rootGroup β := by rw [hroot]; exact hr_mem
  have hr_ne : r ≠ 1 := by
    intro h
    rcases (spSiegel_eq_one_iff hr).mp h with h0 | h0 | h0
    · exact ha1ne h0
    · exact ha2ne h0
    · exact ha12ne h0
  have h2a2 : a₂ + a₂ = (0 : VV) := by
    rw [← two_smul F a₂, CharTwo.two_eq_zero (R := F), zero_smul]
  have h2c : c + c = (0 : VV) := by
    rw [← two_smul F c, CharTwo.two_eq_zero (R := F), zero_smul]
  have hr2 : r * r = 1 := by
    have h := spSiegel_mul (m := m) (x := a₁) (y := a₂) (z := a₂) hB12 hB12
      (show spB m a₂ a₂ = 0 from spForm_self m F a₂) hr hr
    rw [h2a2] at h
    exact spSiegel_ext h (spSiegel_zero_right a₁)
  obtain ⟨t, ht⟩ := spSiegel_exists (m := m) (x := a₁) (y := c) hB1c
  have ht2 : t * t = 1 := by
    have h := spSiegel_mul (m := m) (x := a₁) (y := c) (z := c) hB1c hB1c
      (show spB m c c = 0 from spForm_self m F c) ht ht
    rw [h2c] at h
    exact spSiegel_ext h (spSiegel_zero_right a₁)
  have hcomm_rt : r * t = t * r := by
    have h1' := spSiegel_mul (m := m) (x := a₁) (y := a₂) (z := c) hB12 hB1c hB2c hr ht
    have h2' := spSiegel_mul (m := m) (x := a₁) (y := c) (z := a₂) hB1c hB12 hBc2 ht hr
    rw [add_comm] at h2'
    exact spSiegel_ext h1' h2'
  have hsp_eq : spAltSiegel m F a₁ a₂ = Subgroup.zpowers r := by
    apply le_antisymm
    · intro g hg
      rw [spAltSiegel, Subgroup.mem_comap] at hg
      have hgen : ∀ x ∈ ({x : GL (Fin m ⊕ Fin m) F |
          ∃ cc : F, (x : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) F) =
            1 + cc • (Matrix.vecMulVec a₁ (Matrix.mulVec (spJ m F) a₂) +
              Matrix.vecMulVec a₂ (Matrix.mulVec (spJ m F) a₁))} : Set (GL (Fin m ⊕ Fin m) F)),
          x ∈ (Subgroup.zpowers r).map (StatedSp m F).subtype := by
        rintro x ⟨cc, hcc⟩
        rcases hgf2 cc with rfl | rfl
        · have hx : x = 1 := Units.ext (by rw [hcc, zero_smul, add_zero]; rfl)
          rw [hx]
          exact Subgroup.mem_map_of_mem _ (Subgroup.one_mem _)
        · have hmat : (1 + (1 : F) • (Matrix.vecMulVec a₁ (Matrix.mulVec (spJ m F) a₂) +
              Matrix.vecMulVec a₂ (Matrix.mulVec (spJ m F) a₁)) :
              Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) F) =
              ((r : GL (Fin m ⊕ Fin m) F) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) F) := by
            refine Matrix.ext_iff_mulVec.mpr fun v => ?_
            rw [Matrix.add_mulVec, Matrix.one_mulVec, one_smul, Matrix.add_mulVec,
              Matrix.vecMulVec_mulVec, Matrix.vecMulVec_mulVec]
            have hv : ((r : GL (Fin m ⊕ Fin m) F) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) F) *ᵥ v =
                v + spB m a₂ v • a₁ + spB m a₁ v • a₂ := hr v
            rw [hv]
            simp only [spB_eq_spForm, spForm_β, rckSpP_spJ_dotProduct_comm,
              IsCentralScalar.op_smul_eq_smul, add_assoc]
          have hx : x = (r : GL (Fin m ⊕ Fin m) F) := Units.ext (by rw [hcc, hmat])
          rw [hx]
          exact Subgroup.mem_map_of_mem _ (Subgroup.mem_zpowers r)
      have hle := (Subgroup.closure_le (K := (Subgroup.zpowers r).map (StatedSp m F).subtype)).mpr
        hgen
      have hmem := hle hg
      rw [Subgroup.mem_map] at hmem
      obtain ⟨y, hy, hyg⟩ := hmem
      rwa [← Subtype.ext hyg]
    · intro g hg
      rw [Subgroup.mem_zpowers_iff] at hg
      obtain ⟨k, rfl⟩ := hg
      exact (spAltSiegel m F a₁ a₂).zpow_mem (by rw [← hroot]; exact hr_root) k
  have hrt_ne : r ≠ t := by
    intro h
    have hr_b1 : spAct r b₁ = b₁ + a₂ := by
      rw [hr b₁]
      rw [show spB m a₂ b₁ = 0 from h6, show spB m a₁ b₁ = 1 from h1]; simp
    have ht_b1 : spAct t b₁ = b₁ + spB m c b₁ • a₁ + c := by
      rw [ht b₁]
      rw [show spB m a₁ b₁ = 1 from h1]; simp
    have heq : a₂ = spB m c b₁ • a₁ + c := by
      have hh := hr_b1.symm.trans (h ▸ ht_b1)
      rw [add_assoc] at hh
      exact add_left_cancel hh
    apply hcA
    rw [show c = a₂ - spB m c b₁ • a₁ from by
      rw [eq_sub_iff_add_eq, add_comm]; exact heq.symm]
    exact Submodule.sub_mem A (Submodule.subset_span (by simp))
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
  have ht_ne : t ≠ 1 := by
    intro ht1
    have : spAct t b₁ = b₁ := by rw [ht1]; simp [spAct]
    have hb1 : spAct t b₁ = b₁ + spB m c b₁ • a₁ + c := by
      rw [ht b₁]
      rw [show spB m a₁ b₁ = 1 from h1]; simp
    rw [hb1] at this
    have hzero : spB m c b₁ • a₁ + c = 0 := by
      have hh := congrArg (fun z => z - b₁) this
      rw [add_assoc] at hh
      simpa using hh
    have hcz : c = -(spB m c b₁ • a₁) := eq_neg_of_add_eq_zero_right hzero
    apply hcA
    rw [hcz]
    exact Submodule.neg_mem A (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
  have hrt_ne1 : r * t ≠ 1 := by
    intro h
    have h' : r = t := (mul_left_cancel (h.trans hr2.symm)).symm
    exact hrt_ne h'
  have hrt_ne_r : r * t ≠ r := by
    intro h
    have h' : t = 1 := mul_left_cancel (h.trans (mul_one r).symm)
    exact ht_ne h'
  have hrt_ne_t : r * t ≠ t := by
    intro h
    have h' : r = 1 := mul_right_cancel (h.trans (one_mul t).symm)
    exact hr_ne h'
  have hsup4 : ∀ x ∈ (Subgroup.zpowers r ⊔ Subgroup.zpowers t : Subgroup G),
      x = 1 ∨ x = r ∨ x = t ∨ x = r * t := fun x hx =>
    (CFSG.GH74.GLS.Bg.TwoGroups.mem_sup_zpowers_of_involutions hr2 ht2 hcomm_rt x).mp hx
  have hVcard : Nat.card (Subgroup.zpowers r ⊔ Subgroup.zpowers t : Subgroup G) = 4 := by
    change ((Subgroup.zpowers r ⊔ Subgroup.zpowers t : Subgroup G) : Set G).ncard = 4
    have hset : ((Subgroup.zpowers r ⊔ Subgroup.zpowers t : Subgroup G) : Set G) =
        {1, r, t, r * t} := by
      ext x; constructor
      · intro hx
        rcases hsup4 _ hx with rfl | rfl | rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr (Or.inl rfl))
        · exact Or.inr (Or.inr (Or.inr rfl))
      · intro hx
        rcases hx with hx1 | hx2 | hx3 | hx4
        · rw [hx1]; exact Subgroup.one_mem _
        · rw [hx2]; exact Subgroup.mem_sup_left (Subgroup.mem_zpowers r)
        · rw [hx3]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers t)
        · rw [hx4]; exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_zpowers r))
            (Subgroup.mem_sup_right (Subgroup.mem_zpowers t))
    rw [hset, Set.ncard_insert_of_notMem, Set.ncard_insert_of_notMem, Set.ncard_insert_of_notMem,
      Set.ncard_singleton]
    · exact fun h => hrt_ne_t h.symm
    · intro h; rcases h with h | h
      · exact hrt_ne h
      · exact hrt_ne_r h.symm
    · intro h; rcases h with h | h | h
      · exact hr_ne h.symm
      · exact ht_ne h.symm
      · exact hrt_ne1 h.symm
  have hrt2 : (r * t) * (r * t) = 1 := by
    calc (r * t) * (r * t) = r * (t * r) * t := by group
      _ = r * (r * t) * t := by rw [hcomm_rt.symm]
      _ = (r * r) * (t * t) := by group
      _ = 1 := by rw [hr2, ht2, one_mul]
  have hr_ord : orderOf r = 2 := orderOf_eq_prime (by rw [pow_two]; exact hr2) hr_ne
  have ht_ord : orderOf t = 2 := orderOf_eq_prime (by rw [pow_two]; exact ht2) ht_ne
  have hmem_r : ∀ a ∈ Subgroup.zpowers r, a = 1 ∨ a = r := fun a ha =>
    (Subgroup.mem_zpowers_iff_of_orderOf_eq_two hr_ord).mp ha
  have hmem_t : ∀ a ∈ Subgroup.zpowers t, a = 1 ∨ a = t := fun a ha =>
    (Subgroup.mem_zpowers_iff_of_orderOf_eq_two ht_ord).mp ha
  have hcommST : ∀ a ∈ Subgroup.zpowers r, ∀ b ∈ Subgroup.zpowers t, a * b = b * a := by
    intro a ha b hb
    have ha' : a = 1 ∨ a = r := hmem_r _ ha
    have hb' : b = 1 ∨ b = t := hmem_t _ hb
    rcases ha' with rfl | rfl <;> rcases hb' with rfl | rfl <;> simp [hr2, ht2, hcomm_rt]
  have hpow_r : ∀ a ∈ Subgroup.zpowers r, ∀ c ∈ Subgroup.zpowers r, a * c = c * a := by
    intro a ha c hc
    have ha' : a = 1 ∨ a = r := hmem_r _ ha
    have hc' : c = 1 ∨ c = r := hmem_r _ hc
    rcases ha' with rfl | rfl <;> rcases hc' with rfl | rfl <;> simp [hr2]
  have hpow_t : ∀ a ∈ Subgroup.zpowers t, ∀ c ∈ Subgroup.zpowers t, a * c = c * a := by
    intro a ha c hc
    have ha' : a = 1 ∨ a = t := hmem_t _ ha
    have hc' : c = 1 ∨ c = t := hmem_t _ hc
    rcases ha' with rfl | rfl <;> rcases hc' with rfl | rfl <;> simp [ht2]
  have hVab : IsElemAbelian 2 (Subgroup.zpowers r ⊔ Subgroup.zpowers t : Subgroup G) := by
    constructor
    · rw [isMulCommutative_iff]
      intro x y
      apply Subtype.ext
      push_cast
      obtain ⟨a₁, ha₁, b₁, hb₁, hx'⟩ := CFSG.Quasithin.CommProd.exists_mul_eq hcommST x.2
      obtain ⟨a₂, ha₂, b₂, hb₂, hy'⟩ := CFSG.Quasithin.CommProd.exists_mul_eq hcommST y.2
      rw [← hx', ← hy']
      calc a₁ * b₁ * (a₂ * b₂) = a₁ * (b₁ * a₂) * b₂ := by group
        _ = a₁ * (a₂ * b₁) * b₂ := by rw [← hcommST a₂ ha₂ b₁ hb₁]
        _ = (a₁ * a₂) * (b₁ * b₂) := by group
        _ = (a₂ * a₁) * (b₂ * b₁) := by rw [hpow_r a₁ ha₁ a₂ ha₂, hpow_t b₁ hb₁ b₂ hb₂]
        _ = a₂ * b₂ * (a₁ * b₁) := by
          calc (a₂ * a₁) * (b₂ * b₁) = a₂ * (a₁ * b₂) * b₁ := by group
            _ = a₂ * (b₂ * a₁) * b₁ := by rw [← hcommST a₁ ha₁ b₂ hb₂]
            _ = a₂ * b₂ * (a₁ * b₁) := by group
    · intro x hx
      rcases hsup4 _ hx with hx' | hx' | hx' | hx'
      · rw [hx']; simp
      · rw [hx']; simpa [pow_two] using hr2
      · rw [hx']; simpa [pow_two] using ht2
      · rw [hx']; simpa [pow_two] using hrt2
  have hB1_2c : spB m a₁ (a₂ + c) = 0 := by
    have hh := (spForm m F).add_right a₁ a₂ c
    rw [show (spForm m F).β a₁ a₂ = 0 from hB12,
      show (spForm m F).β a₁ c = 0 from hB1c, add_zero] at hh
    exact hh
  have h2cne : a₂ + c ≠ 0 := by
    intro h0
    have h1 : c = a₂ := add_left_cancel (h0.trans h2a2.symm)
    exact hcA (h1 ▸ Submodule.subset_span (by simp))
  have hne_c : a₁ ≠ c := fun h => hcA (h ▸ Submodule.subset_span (by simp))
  have hne_2c : a₁ ≠ a₂ + c := by
    intro h
    have : c = a₁ - a₂ := by rw [h]; abel
    exact hcA (this ▸ Submodule.sub_mem A (Submodule.subset_span (by simp))
      (Submodule.subset_span (by simp)))
  have hp12 : pairedSympForm F m a₁ a₂ = 0 := by
    rw [pairedSympForm_apply, ← dotProduct_spJ_mulVec]; exact hB12
  have hp1c : pairedSympForm F m a₁ c = 0 := by
    rw [pairedSympForm_apply, ← dotProduct_spJ_mulVec]; exact hB1c
  have hp1_2c : pairedSympForm F m a₁ (a₂ + c) = 0 := by
    rw [pairedSympForm_apply, ← dotProduct_spJ_mulVec]; exact hB1_2c
  obtain ⟨jt, hjt⟩ := exists_smul_pair_of_spOrth (K := F) (r := m) (u := a₁) (v := a₂)
    (u' := a₁) (v' := c) ha1ne ha2ne ha1ne hcne
    (rckSpP_ofVec_ne ha1ne ha2ne ha12ne) (rckSpP_ofVec_ne ha1ne hcne hne_c) hp12 hp1c
  obtain ⟨jrt, hjrt⟩ := exists_smul_pair_of_spOrth (K := F) (r := m) (u := a₁) (v := a₂)
    (u' := a₁) (v' := a₂ + c) ha1ne ha2ne ha1ne h2cne
    (rckSpP_ofVec_ne ha1ne ha2ne ha12ne) (rckSpP_ofVec_ne ha1ne h2cne hne_2c) hp12 hp1_2c
  have hjt1 : spAct jt a₁ = a₁ := rckSpP_spAct_eq_of_smul_ofVec_eq ha1ne ha1ne hjt.1
  have hjt2 : spAct jt a₂ = c := rckSpP_spAct_eq_of_smul_ofVec_eq ha2ne hcne hjt.2
  have hjrt1 : spAct jrt a₁ = a₁ := rckSpP_spAct_eq_of_smul_ofVec_eq ha1ne ha1ne hjrt.1
  have hjrt2 : spAct jrt a₂ = a₂ + c := rckSpP_spAct_eq_of_smul_ofVec_eq ha2ne h2cne hjrt.2
  have ht_conj : t = jt * r * jt⁻¹ := by
    have hconj' : SpSiegel a₁ c (jt * r * jt⁻¹) := by
      have := spSiegel_conj hr jt
      rwa [hjt1, hjt2] at this
    exact spSiegel_ext ht hconj'
  have hrt_conj : r * t = jrt * r * jrt⁻¹ := by
    have hrt' : SpSiegel a₁ (a₂ + c) (r * t) := spSiegel_mul hB12 hB1c hB2c hr ht
    have hconj' : SpSiegel a₁ (a₂ + c) (jrt * r * jrt⁻¹) := by
      have := spSiegel_conj hr jrt
      rwa [hjrt1, hjrt2] at this
    exact spSiegel_ext hrt' hconj'
  have hconj : ∀ v ∈ (Subgroup.zpowers r ⊔ Subgroup.zpowers t : Subgroup G), v ≠ 1 →
      ∃ j : G, v = j * r * j⁻¹ := by
    intro v hv hv1
    rcases hsup4 _ hv with h1v | h2v | h3v | h4v
    · exact absurd h1v hv1
    · exact ⟨1, by rw [h2v]; simp⟩
    · exact ⟨jt, by rw [h3v]; exact ht_conj⟩
    · exact ⟨jrt, by rw [h4v]; exact hrt_conj⟩
  have horder_r : orderOf r = 2 := by
    rw [orderOf_eq_iff (by norm_num : 0 < 2)]
    refine ⟨?_, ?_⟩
    · simpa [pow_two] using hr2
    · intro k hk hk2
      have : k = 1 := by omega
      subst this
      simpa using hr_ne
  have hpp : SpPlanePair m F a₁ a₂ b₁ b₂ := ⟨h1, h2, h3, h4, h5, h6⟩
  have hcent : Subgroup.centralizer ({r} : Set G) =
      CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.stabilizer m F A := by
    rw [← normalizer_zpowers_eq_centralizer_of_orderOf_eq_two horder_r, ← hsp_eq, hAdef]
    exact normalizer_spAltSiegel_eq_stabilizer hpp
  have hpCore : pCoreOf 2 (Subgroup.centralizer ({r} : Set G)) ≤ sprad A hW := by
    rw [hcent]
    exact pCoreOf_stabilizer_le_sprad hpp (hW := hW)
  have hcomm_le : ∀ y ∈ pCoreOf 2 (Subgroup.centralizer ({r} : Set G)),
      ∀ v ∈ (Subgroup.zpowers r ⊔ Subgroup.zpowers t : Subgroup G),
      y * v * y⁻¹ * v⁻¹ ∈ Subgroup.zpowers r := by
    intro y hy v hv
    have hyrad : y ∈ sprad A hW := hpCore hy
    have hyA : ∀ w ∈ A, spAct y w = w := fun w hw => (mem_rad.mp hyrad).1 w hw
    have hyperp : ∀ w ∈ (spForm m F).perp A, spAct y w - w ∈ A :=
      fun w hw => (mem_rad.mp hyrad).2 w hw
    have hyr : spAct y a₁ = a₁ := hyA a₁ (Submodule.subset_span (by simp))
    have hya₂ : spAct y a₂ = a₂ := hyA a₂ (Submodule.subset_span (by simp))
    have hyr_conj : y * r * y⁻¹ = r := by
      have h := spSiegel_conj hr y
      rw [hyr, hya₂] at h
      exact spSiegel_ext h hr
    set u : VV := spAct y c - c with hudef
    have huA : u ∈ A := hyperp c hc_perp
    have hBu1 : spB m u a₁ = 0 :=
      ((spForm m F).mem_perp.mp (hW (Submodule.subset_span (by simp)))) u huA
    have hBu2 : spB m u a₂ = 0 :=
      ((spForm m F).mem_perp.mp (hW (Submodule.subset_span (by simp)))) u huA
    have hB1u : spB m a₁ u = 0 := (spForm m F).refl u a₁ hBu1
    have hB2u : spB m a₂ u = 0 := (spForm m F).refl u a₂ hBu2
    have hBuc : spB m u c = 0 := ((spForm m F).mem_perp.mp hc_perp) u huA
    have hBcu : spB m c u = 0 := (spForm m F).refl u c hBuc
    have hyc : spAct y c = c + u := by rw [hudef]; abel
    obtain ⟨s, hs⟩ := spSiegel_exists (m := m) (x := a₁) (y := u) hB1u
    have hyt_conj : y * t * y⁻¹ = t * s := by
      exact (spSiegel_ext (spSiegel_mul hB1c hB1u hBcu ht hs) (by
        have h := spSiegel_conj ht y
        rwa [hyr, hyc] at h)).symm
    have hs_mem : s ∈ Subgroup.zpowers r := by
      obtain ⟨α, βf, hαβ⟩ := Submodule.mem_span_pair.mp huA
      have hs' : SpSiegel a₁ (α • a₁ + βf • a₂) s := by rw [hαβ]; exact hs
      rcases hgf2 α with rfl | rfl <;>
        rcases hgf2 βf with rfl | rfl
      · have : s = 1 := spSiegel_ext hs' (by simpa using spSiegel_zero_right (m := m) (x := a₁))
        rw [this]; exact Subgroup.one_mem _
      · have : s = r := spSiegel_ext hs' (by simpa using hr)
        rw [this]; exact Subgroup.mem_zpowers r
      · have : s = 1 := spSiegel_ext hs' (by simpa using spSiegel_self (m := m) (x := a₁))
        rw [this]; exact Subgroup.one_mem _
      · have hr' : SpSiegel a₁ (a₁ + a₂) r := by
          have h := spSiegel_mul (x := a₁) (y := a₁) (z := a₂)
            (show spB m a₁ a₁ = 0 from spForm_self m F a₁) hB12 hB12
            (spSiegel_self a₁) hr
          simpa using h
        have : s = r := spSiegel_ext hs' (by simpa using hr')
        rw [this]; exact Subgroup.mem_zpowers r
    have hst_comm : t * s = s * t := by
      have h1 := spSiegel_mul (x := a₁) (y := c) (z := u) hB1c hB1u hBcu ht hs
      have h2 := spSiegel_mul (x := a₁) (y := u) (z := c) hB1u hB1c hBuc hs ht
      rw [add_comm] at h2
      exact spSiegel_ext h1 h2
    have hsr_comm : r * s = s * r := by
      have h1 := spSiegel_mul (x := a₁) (y := a₂) (z := u) hB12 hB1u hB2u hr hs
      have h2 := spSiegel_mul (x := a₁) (y := u) (z := a₂) hB1u hB12 hBu2 hs hr
      rw [add_comm] at h2
      exact spSiegel_ext h1 h2
    rcases hsup4 _ hv with hv1 | hv2 | hv3 | hv4
    · rw [hv1, mul_one, inv_one, mul_one, mul_inv_cancel]; exact Subgroup.one_mem _
    · rw [hv2, hyr_conj, mul_inv_cancel]; exact Subgroup.one_mem _
    · rw [hv3, show y * t * y⁻¹ * t⁻¹ = (y * t * y⁻¹) * t⁻¹ from by group, hyt_conj,
        show t * s * t⁻¹ = s from by rw [hst_comm]; group]
      exact hs_mem
    · have hterm : y * (r * t) * y⁻¹ * (r * t)⁻¹ = s := by
        rw [mul_inv_rev]
        have h1 : y * (r * t) * y⁻¹ = (y * r * y⁻¹) * (y * t * y⁻¹) := by
          change MulAut.conj y (r * t) = MulAut.conj y r * MulAut.conj y t
          rw [map_mul]
        rw [h1, hyr_conj, hyt_conj, hst_comm]
        rw [show r * (s * t) * (t⁻¹ * r⁻¹) = r * s * r⁻¹ by group, hsr_comm]
        group
      rw [hv4, hterm]
      exact hs_mem
  exact ⟨r, Subgroup.zpowers r ⊔ Subgroup.zpowers t, hr_root, hr_ne,
    Subgroup.mem_sup_left (Subgroup.mem_zpowers r), hVab, hVcard, hconj, hcomm_le⟩

end CFSG.StandardType.RCKK1IIISp
