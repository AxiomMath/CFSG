module

public import CFSG.RankThree.GF2n.Stroth80.Sec310SLDirect
public import CFSG.RankThree.GF2n.Stroth80.Sec311Lines

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank CFSG.RankThree.GF2n
open scoped commutatorElement Matrix

theorem stroth310SLTransvConj_of_34 (h34 : Stroth34Statement) :
    ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
      Sec5Hyp hc n t → Rt M (LB M Q B) t ≠ LB M Q B → Vt M (LB M Q B) B Z t ≤ QB B →
      ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2), Nat.card K = Nat.card Z ∧
        ∃ m : ℕ, 2 ≤ m ∧ ∃ φ : ↥(Rt M (LB M Q B) t) →* GL (Fin m) K,
          φ.ker = (hc.CN t).subgroupOf (Rt M (LB M Q B) t) ∧
          SectionAct K (Rt M (LB M Q B) t) (Vt M (LB M Q B) B Z t) Z φ
            (fun g => (g : Matrix (Fin m) (Fin m) K)) ∧ φ.range = StatedSL m K ∧
          ∃ u : G → (Fin m → K),
            (∀ m' ∈ M, t ∈ conjSubgroup m' (LB M Q B) → u m' ≠ 0 ∧
              (∀ l : ↥(Rt M (LB M Q B) t), (l : G) ∈ conjSubgroup m' (LB M Q B) →
                ∃ f : Fin m → K, f ⬝ᵥ u m' = 0 ∧
                  (φ l : Matrix (Fin m) (Fin m) K) = 1 + Matrix.vecMulVec (u m') f) ∧
              (∀ f : Fin m → K, f ⬝ᵥ u m' = 0 → ∃ l : ↥(Rt M (LB M Q B) t),
                (l : G) ∈ conjSubgroup m' (LB M Q B) ∧
                  (φ l : Matrix (Fin m) (Fin m) K) = 1 + Matrix.vecMulVec (u m') f)) ∧
            (∀ m₁ ∈ M, ∀ m₂ ∈ M, t ∈ conjSubgroup m₁ (LB M Q B) →
              t ∈ conjSubgroup m₂ (LB M Q B) → (∃ c : K, u m₂ = c • u m₁) →
                conjSubgroup m₁ (LB M Q B) = conjSubgroup m₂ (LB M Q B)) := by
  classical
  intro G _ _ M Q Z B hc n t hs hR hV
  have h35all := stroth_3_5 h34 hc hs.width hs.n_gt hs.noA2 hs.gen
  have h35 := h35all.2.1
  obtain ⟨n', γ, M₀, -, h⟩ := stroth_globalModelDataGF hc.hyp
  set V := Vt M (LB M Q B) B Z t with hVdef
  set R := Rt M (LB M Q B) t with hRdef
  have hS : ∀ (c : GaloisField 2 n') (e : M₀.E), e ∈ M₀.img V → c • e ∈ M₀.img V :=
    fun c e he => hc.smul_mem_img_Vt h t c he
  obtain ⟨m, φ, hnorm, ψ, c, hker, hequiv, -, -, hSeq⟩ :=
    exists_natural_data_of_subspace hc.hyp (hc.Vt_le_Q t) sec39_Z_le_Vt (hc.Rt_le_H0 t)
      (hc.Rt_normalizes_Vt hs.mem) (fun _ => Ctx.mem_CN (hc := hc)) h hS
  have hm2 : 2 ≤ m := by
    have := hc.two_le_finrank_Vt h35 hs.mem hR h hS
    rwa [c.finrank_eq, Module.finrank_fin_fun] at this
  have hconj : ∀ m' ∈ M, t ∈ conjSubgroup m' (LB M Q B) → ∃ (u : Fin m → GaloisField 2 n')
      (b : M₀.E) (hb : b ∈ imgSub M₀ V hS), u = c ⟨b, hb⟩ ∧ u ≠ 0 ∧
      (∀ v, v ∈ M₀.img (conjSubgroup m' B) ↔ ∃ s : GaloisField 2 n', v = s • b) ∧
      (∀ l : ↥R, (l : G) ∈ conjSubgroup m' (LB M Q B) →
        ∃ f : Fin m → GaloisField 2 n', f ⬝ᵥ u = 0 ∧
          (φ l : Matrix (Fin m) (Fin m) (GaloisField 2 n')) = 1 + Matrix.vecMulVec u f) ∧
      (∀ f : Fin m → GaloisField 2 n', f ⬝ᵥ u = 0 → ∃ l : ↥R,
        (l : G) ∈ conjSubgroup m' (LB M Q B) ∧
          (φ l : Matrix (Fin m) (Fin m) (GaloisField 2 n')) = 1 + Matrix.vecMulVec u f) := by
    intro m' hm' htm'
    have hC : Ctx M Q Z (conjSubgroup m' B) := hc.conj_of_mem hm'
    have hnoC : NoA2 Q Z (LB M Q (conjSubgroup m' B)) := hc.noA2_conj hs.noA2 hm'
    have h35C := stroth_3_5 h34 hC hs.width hs.n_gt hnoC (hs.gen.conj_of_mem hm')
    have hVC : V ≤ QB (conjSubgroup m' B) :=
      hc.Vt_le_QB_conj hs.width hs.n_gt hs.noA2 h35 hs.mem hV hm' htm'
    have hCV : conjSubgroup m' B ≤ V := sec39_conjB_le_Vt hm' htm'
    have hLC : LB M Q (conjSubgroup m' B) = conjSubgroup m' (LB M Q B) := hc.LB_conj hm'
    have hLR : LB M Q (conjSubgroup m' B) ≤ R := by
      rw [hLC]
      exact conjSubgroup_le_Rt hm' htm'
    obtain ⟨b, hbV', -, hu0, hBb, hP1, hP2, -⟩ := hC.matrix_elation_data hs.width hs.n_gt hnoC
      h35C.2.2.1 h35C.2.2.2 h hCV (le_inf (hc.Vt_le_Q t) hVC) hS (hc.Rt_le_H0 t)
      (hc.Rt_normalizes_Vt hs.mem) hLR φ c hSeq
    refine ⟨c ⟨b, hbV'⟩, b, hbV', rfl, hu0, hBb, fun l hl => ?_, fun f hf => ?_⟩
    · obtain ⟨f, hf0, hfm⟩ := hP1 (l : G) (hLC ▸ hl)
      exact ⟨f, hf0, hfm⟩
    · obtain ⟨l, hl, hfm⟩ := hP2 f hf
      exact ⟨⟨l, hLR hl⟩, hLC ▸ hl, hfm⟩
  choose! u bb hbb hu using hconj
  have hLRB : LB M Q B ≤ R := le_Rt (M := M) (LB M Q B) hs.mem
  have hirr : NatIrred φ.range := hc.natIrred_of_data h35 hs.mem h hS φ c hSeq
  have hgen : GenByTransvLines φ.range := by
    apply le_antisymm
    · let Sset : Set (GL (Fin m) (GaloisField 2 n')) := {g | ∃ v f : Fin m → GaloisField 2 n',
        v ≠ 0 ∧ f ≠ 0 ∧ f ⬝ᵥ v = 0 ∧ (g : Matrix (Fin m) (Fin m) (GaloisField 2 n')) =
          1 + Matrix.vecMulVec v f ∧ ∀ c : GaloisField 2 n', ∃ h ∈ φ.range,
            (h : Matrix (Fin m) (Fin m) (GaloisField 2 n')) = 1 + c • Matrix.vecMulVec v f}
      let Γ : Subgroup G := ((Subgroup.closure Sset).comap φ).map R.subtype
      have hRΓ : R ≤ Γ := by
        refine iSup₂_le fun m' hm' => iSup_le fun htm' => ?_
        intro l hl
        have hlR : l ∈ R := conjSubgroup_le_Rt hm' htm' hl
        refine ⟨⟨l, hlR⟩, ?_, rfl⟩
        obtain ⟨-, hu0, -, hP1, hP2⟩ := hu m' hm' htm'
        obtain ⟨f, hf0, hfm⟩ := hP1 ⟨l, hlR⟩ hl
        show φ ⟨l, hlR⟩ ∈ Subgroup.closure Sset
        by_cases hf : f = 0
        · have : φ ⟨l, hlR⟩ = 1 := by
            apply Units.ext
            rw [hfm, hf]
            simp
          rw [this]
          exact Subgroup.one_mem _
        · refine Subgroup.subset_closure ⟨u m', f, hu0, hf, hf0, hfm, fun a => ?_⟩
          have ha : (a • f) ⬝ᵥ u m' = 0 := by rw [smul_dotProduct, hf0, smul_zero]
          obtain ⟨l', hl'', hmat⟩ := hP2 (a • f) ha
          refine ⟨φ l', ⟨_, rfl⟩, ?_⟩
          rw [hmat]
          congr 1
          ext i j
          simp [Matrix.vecMulVec_apply, mul_left_comm]
      rintro _ ⟨r, rfl⟩
      obtain ⟨r', hr', hrr⟩ := hRΓ r.2
      have : r' = r := Subtype.ext hrr
      rw [← this]
      exact hr'
    · refine (Subgroup.closure_le φ.range).mpr ?_
      rintro g ⟨v, f, -, -, -, hg, hK⟩
      obtain ⟨h', hh', hh'g⟩ := hK 1
      rw [one_smul] at hh'g
      have : h' = g := Units.ext (hh'g.trans hg.symm)
      exact this ▸ hh'
  have h1M : (1 : G) ∈ M := M.one_mem
  have h1t : t ∈ conjSubgroup (1 : G) (LB M Q B) := by rw [conjSubgroup_one]; exact hs.mem
  obtain ⟨-, huB0, -, hB1, hB2⟩ := hu 1 h1M h1t
  have hLB1 : ∀ l : G, l ∈ conjSubgroup (1 : G) (LB M Q B) ↔ l ∈ LB M Q B := fun l => by
    rw [conjSubgroup_one]
  have hcount : Nat.card (GaloisField 2 n') ^ (m - 1) ≤
      Nat.card ↥(((LB M Q B).subgroupOf R).map φ) := by
    rw [← card_dotProduct_ker huB0]
    let F : {f : Fin m → GaloisField 2 n' // f ⬝ᵥ u 1 = 0} →
        ↥(((LB M Q B).subgroupOf R).map φ) :=
      fun f => ⟨φ (hB2 f.1 f.2).choose,
        ⟨(hB2 f.1 f.2).choose, Subgroup.mem_subgroupOf.mpr
          ((hLB1 _).mp (hB2 f.1 f.2).choose_spec.1), rfl⟩⟩
    refine Nat.card_le_card_of_injective F ?_
    intro f f' hff
    have h1 := congrArg (fun x : ↥(((LB M Q B).subgroupOf R).map φ) =>
      ((x : GL (Fin m) (GaloisField 2 n')) : Matrix (Fin m) (Fin m) (GaloisField 2 n'))) hff
    simp only [F] at h1
    rw [(hB2 f.1 f.2).choose_spec.2, (hB2 f'.1 f'.2).choose_spec.2] at h1
    obtain ⟨i, hi⟩ : ∃ i, u 1 i ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact huB0 (funext hcon)
    refine Subtype.ext (funext fun j => ?_)
    have h2 := congrFun (congrFun h1 i) j
    simp only [Matrix.add_apply, Matrix.vecMulVec_apply] at h2
    exact mul_left_cancel₀ hi (add_left_cancel h2)
  have hΛX : ((LB M Q B).subgroupOf R).map φ ≤ φ.range := Subgroup.map_le_range _ _
  have hΛ : ∀ g ∈ ((LB M Q B).subgroupOf R).map φ, ∀ x : Fin m → GaloisField 2 n',
      ∃ c : GaloisField 2 n', (g : Matrix (Fin m) (Fin m) (GaloisField 2 n')) *ᵥ x - x =
        c • u 1 := by
    rintro g ⟨l, hl, rfl⟩ x
    obtain ⟨f, -, hf⟩ := hB1 l ((hLB1 _).mpr (Subgroup.mem_subgroupOf.mp hl))
    refine ⟨f ⬝ᵥ x, ?_⟩
    rw [hf, mulVec_one_add_vecMulVec]
    abel
  have hrange : φ.range = StatedSL m (GaloisField 2 n') :=
    eq_statedSL_of_full_centre hm2 φ.range hirr hgen _ hΛX huB0 hΛ hcount
  refine ⟨GaloisField 2 n', inferInstance, inferInstance, inferInstance, h.card, m, hm2, φ, hker,
    ⟨hc.Rt_normalizes_Vt hs.mem, hnorm, ψ, hequiv⟩, hrange, u, fun m' hm' htm' => ?_, ?_⟩
  · obtain ⟨-, hu0, -, hP1, hP2⟩ := hu m' hm' htm'
    exact ⟨hu0, hP1, hP2⟩
  · intro m₁ hm₁ m₂ hm₂ ht₁ ht₂ ⟨a, ha⟩
    obtain ⟨hu₁, hu0₁, hline₁, -, -⟩ := hu m₁ hm₁ ht₁
    obtain ⟨hu₂, hu0₂, hline₂, -, -⟩ := hu m₂ hm₂ ht₂
    have ha0 : a ≠ 0 := by
      rintro rfl
      exact hu0₂ (by rw [ha, zero_smul])
    have hc1 : c ⟨bb m₂, hbb m₂ hm₂ ht₂⟩ = c (a • ⟨bb m₁, hbb m₁ hm₁ ht₁⟩) := by
      rw [map_smul, ← hu₁, ← hu₂, ha]
    have hb21 := congrArg Subtype.val (c.injective hc1)
    simp only [SetLike.val_smul] at hb21
    have hline : ∀ v, v ∈ M₀.img (conjSubgroup m₁ B) ↔ v ∈ M₀.img (conjSubgroup m₂ B) := by
      intro v
      rw [hline₁, hline₂]
      constructor
      · rintro ⟨s, rfl⟩
        refine ⟨s * a⁻¹, ?_⟩
        rw [hb21, smul_smul, mul_assoc, inv_mul_cancel₀ ha0, mul_one]
      · rintro ⟨s, rfl⟩
        exact ⟨s * a, by rw [hb21, smul_smul]⟩
    exact hc.conj_LB_eq_of_img_eq (M₀ := M₀) hm₁ hm₂ hline

end CFSG.RankThree.GF2n.Stroth80
