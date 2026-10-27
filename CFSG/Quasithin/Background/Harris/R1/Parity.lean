module

public import CFSG.Quasithin.Background.Harris.R1.ParityPerm
public import CFSG.Quasithin.Background.Harris.R1.PermAlt
public import CFSG.Quasithin.Background.Harris.R1.QbetaKer
public import CFSG.Quasithin.Background.Harris.R1.ParityGram
public import CFSG.Quasithin.Recognition.SzR1Prep

public section

namespace CFSG.Quasithin.Background.Harris.R1

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.SzR1
  CFSG.Quasithin.F7

variable {G : Type} [Group G] [Finite G] {K1 L2 S Zs : Subgroup G} {Ω : Type}

theorem g_move_of_not_mem_normalizer (C : FamCtx K1 L2 S Zs Ω) {i₀ j₀ : Ω} (hij : i₀ ≠ j₀) {g : G}
    (hg : g ∉ Subgroup.normalizer (Zs : Set G)) : g * C.cm i₀ j₀ * g⁻¹ ≠ C.cm i₀ j₀ := by
  intro hfix
  apply hg
  rw [Subgroup.mem_normalizer_iff]
  intro h
  have hcsq := C.Zs_sq (C.cm_mem i₀ j₀)
  constructor
  · intro hh
    rcases Zs_eq_one_or C hij hh with rfl | rfl
    · simp
    · rw [hfix]; exact hh
  · intro hh
    rcases Zs_eq_one_or C hij hh with h1 | h1
    · have : h = 1 := by
        have : g * h * g⁻¹ = 1 := h1
        simpa using this
      rw [this]; exact Zs.one_mem
    · have : h = C.cm i₀ j₀ := by
        have e : g * h * g⁻¹ = g * C.cm i₀ j₀ * g⁻¹ := by rw [h1, hfix]
        simpa using e
      rw [this]; exact C.cm_mem i₀ j₀


theorem pCore_centralizes_Vf (C : FamCtx K1 L2 S Zs Ω) {q : G} (hq : q ∈ pCoreOf 2 (L2 ⊔ S)) :
    ∀ v ∈ C.D.Vf (conjClosure Zs L2) C.D.pt, v * q = q * v := by
  intro v hv
  rw [C.Vf_pt] at hv
  exact (C.mem_pCore_iff.mp hq).2 v hv

theorem pCore_conj_vBeta (C : FamCtx K1 L2 S Zs Ω) {g : G} (hgP : g ∈ L2 ⊔ S) {q : G}
    (hq : q ∈ pCoreOf 2 (L2 ⊔ S)) {y : G} (hy : y ∈ conjSub g (vBeta K1 L2 S Zs)) :
    q * y * q⁻¹ ∈ conjSub g (vBeta K1 L2 S Zs) := by
  have hgQ : g ∈ Subgroup.normalizer (pCoreOf 2 (L2 ⊔ S) : Set G) :=
    le_normalizer_pCoreOf 2 (L2 ⊔ S) hgP
  have hs : g⁻¹ * q * g ∈ pCoreOf 2 (L2 ⊔ S) := by
    have := (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer _).inv_mem hgQ) q).mp hq
    simpa [mul_assoc] using this
  have hsS : g⁻¹ * q * g ∈ S := C.pCore_le_S hs
  rw [mem_conjSub] at hy ⊢
  have := (Subgroup.mem_normalizer_iff.mp (S_le_normalizer_vBeta K1 L2 S Zs hsS) _).mp hy
  have e : g⁻¹ * (q * y * q⁻¹) * g = (g⁻¹ * q * g) * (g⁻¹ * y * g) * (g⁻¹ * q * g)⁻¹ := by group
  rw [e]
  exact this

variable [Fintype Ω] [DecidableEq Ω]

theorem mem_Vf_of_mem_inter (C : FamCtx K1 L2 S Zs Ω)
    (hΩ : Fintype.card Ω = 5)
    (hcen : ∀ x ∈ vBeta K1 L2 S Zs, (∀ u ∈ vBeta K1 L2 S Zs, x * u = u * x) → x ∈ Zs)
    {g : G} (hgZ : g ∉ Subgroup.normalizer (Zs : Set G)) {x : G}
    (hxW : x ∈ vBeta K1 L2 S Zs) (hxQ : x ∈ pCoreOf 2 (L2 ⊔ S))
    (hxWg : x ∈ conjSub g (vBeta K1 L2 S Zs)) : x ∈ C.D.Vf (conjClosure Zs L2) C.D.pt := by
  obtain ⟨i₀, j₀, hij₀⟩ := Fintype.exists_pair_of_one_lt_card (by omega : 1 < Fintype.card Ω)
  have hx2Z : x * x ∈ Zs := FamCtxLemmas.sq_mem_Zs C hij₀ hxW
  have hx2Zg : x * x ∈ conjSub g Zs := by
    have h1 : (g⁻¹ * x * g) * (g⁻¹ * x * g) ∈ Zs :=
      FamCtxLemmas.sq_mem_Zs C hij₀ (mem_conjSub.mp hxWg)
    rw [mem_conjSub]
    have e : g⁻¹ * (x * x) * g = (g⁻¹ * x * g) * (g⁻¹ * x * g) := by group
    rw [e]; exact h1
  have hx2 : x * x = 1 := by
    rcases Zs_eq_one_or C hij₀ hx2Z with h1 | h1
    · exact h1
    · exfalso
      rw [h1, mem_conjSub] at hx2Zg
      have e1 : g * (g⁻¹ * C.cm i₀ j₀ * g) * g⁻¹ = C.cm i₀ j₀ := by group
      rcases Zs_eq_one_or C hij₀ hx2Zg with h2 | h2
      · rw [h2] at e1
        exact C.cm_ne_one hij₀ (by simpa using e1.symm)
      · rw [h2] at e1
        exact g_move_of_not_mem_normalizer C hij₀ hgZ e1
  have hxc : x * C.zf C.D.pt = C.zf C.D.pt * x :=
    (pCore_centralizes_Vf C hxQ (C.zf C.D.pt) (C.zf_mem C.D.pt)).symm
  exact FamCtxLemmas.mem_Vf_pt_of_sq_eq_one C hΩ hcen hxW hxc hx2

theorem comm_mem_Vf (C : FamCtx K1 L2 S Zs Ω)
    (hΩ : Fintype.card Ω = 5)
    (hcen : ∀ x ∈ vBeta K1 L2 S Zs, (∀ u ∈ vBeta K1 L2 S Zs, x * u = u * x) → x ∈ Zs)
    {g : G} (hgP : g ∈ L2 ⊔ S) (hgZ : g ∉ Subgroup.normalizer (Zs : Set G)) {a b : G}
    (haW : a ∈ vBeta K1 L2 S Zs) (haQ : a ∈ pCoreOf 2 (L2 ⊔ S))
    (hbQ : b ∈ pCoreOf 2 (L2 ⊔ S)) (hbW : b ∈ conjSub g (vBeta K1 L2 S Zs)) :
    b * a * b⁻¹ * a⁻¹ ∈ C.D.Vf (conjClosure Zs L2) C.D.pt := by
  set Q := pCoreOf 2 (L2 ⊔ S) with hQ
  have hbS : b ∈ S := C.pCore_le_S hbQ
  have hSW : ∀ s ∈ S, ∀ w ∈ vBeta K1 L2 S Zs, s * w * s⁻¹ ∈ vBeta K1 L2 S Zs :=
    fun s hs w hw => (Subgroup.mem_normalizer_iff.mp (S_le_normalizer_vBeta K1 L2 S Zs hs) w).mp hw
  set x := a * b * a⁻¹ * b⁻¹ with hx
  have hxW : x ∈ vBeta K1 L2 S Zs := by
    have h1 : b * a⁻¹ * b⁻¹ ∈ vBeta K1 L2 S Zs := hSW b hbS _ ((vBeta K1 L2 S Zs).inv_mem haW)
    have : x = a * (b * a⁻¹ * b⁻¹) := by rw [hx]; group
    rw [this]; exact (vBeta K1 L2 S Zs).mul_mem haW h1
  have hxQ : x ∈ Q := Q.mul_mem (Q.mul_mem (Q.mul_mem haQ hbQ) (Q.inv_mem haQ)) (Q.inv_mem hbQ)
  have hxWg : x ∈ conjSub g (vBeta K1 L2 S Zs) := by
    have h1 : a * b * a⁻¹ ∈ conjSub g (vBeta K1 L2 S Zs) := pCore_conj_vBeta C hgP haQ hbW
    exact (conjSub g _).mul_mem h1 ((conjSub g _).inv_mem hbW)
  have hxV := mem_Vf_of_mem_inter C hΩ hcen hgZ hxW hxQ hxWg
  have e : b * a * b⁻¹ * a⁻¹ = x⁻¹ := by rw [hx]; group
  rw [e]
  exact (C.D.Vf (conjClosure Zs L2) C.D.pt).inv_mem hxV

theorem exists_mul_of_mem_conj (C : FamCtx K1 L2 S Zs Ω)
    (hΩ : Fintype.card Ω = 5) (hL24 : IsL2Quot 2 (OTwoQuot K1))
    (hcen : ∀ x ∈ vBeta K1 L2 S Zs, (∀ u ∈ vBeta K1 L2 S Zs, x * u = u * x) → x ∈ Zs)
    {g : G} (hgP : g ∈ L2 ⊔ S) (hgZ : g ∉ Subgroup.normalizer (Zs : Set G)) {b : G}
    (hbQ : b ∈ pCoreOf 2 (L2 ⊔ S)) (hbW : b ∈ conjSub g (vBeta K1 L2 S Zs)) :
    ∃ k ∈ K1, ∃ m ∈ C.kerM, b = k * m := by
  have hbS : b ∈ S := C.pCore_le_S hbQ
  have hbsup : b ∈ K1 ⊔ S := Subgroup.mem_sup_right hbS
  have hcom : ∀ i j : Ω, i ≠ C.D.pt → j ≠ C.D.pt → i ≠ j →
      b * (C.zf i * C.zf j) * b⁻¹ * (C.zf i * C.zf j)⁻¹ ∈ C.D.Vf (conjClosure Zs L2) C.D.pt := by
    intro i j hi hj hij
    exact comm_mem_Vf C hΩ hcen hgP hgZ ((vBeta K1 L2 S Zs).mul_mem (C.zf_mem_U i) (C.zf_mem_U j))
      (C.zf_mul_mem_pCore hi hj) hbQ hbW
  have hsign := FamCtxLemmas.sign_permHom_eq_one C hΩ hbsup (pCore_centralizes_Vf C hbQ) hcom
  obtain ⟨k, hk⟩ := exists_act_eq C hΩ hL24 _ hsign
  refine ⟨(k : G), k.2, (k : G)⁻¹ * b, ?_, by group⟩
  rw [← permHom_eq_one_iff C ⟨(k : G)⁻¹ * b, (K1 ⊔ S).mul_mem ((K1 ⊔ S).inv_mem
    (Subgroup.mem_sup_left k.2)) hbsup⟩]
  have h1 : permHom C ⟨(k : G), Subgroup.mem_sup_left k.2⟩ = permHom C ⟨b, hbsup⟩ := by
    rw [permHom_K1, hk]
  have e : (⟨(k : G)⁻¹ * b, (K1 ⊔ S).mul_mem ((K1 ⊔ S).inv_mem (Subgroup.mem_sup_left k.2))
      hbsup⟩ : ↥(K1 ⊔ S)) = (⟨(k : G), Subgroup.mem_sup_left k.2⟩ : ↥(K1 ⊔ S))⁻¹ * ⟨b, hbsup⟩ := rfl
  rw [e, map_mul, map_inv, h1, inv_mul_cancel]

end CFSG.Quasithin.Background.Harris.R1
