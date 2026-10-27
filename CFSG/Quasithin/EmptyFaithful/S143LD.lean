module

public import CFSG.Quasithin.EmptyFaithful.S143LB
public import CFSG.Quasithin.Background.A1cModuleDefs
public import CFSG.Quasithin.EmptyFaithful.S143KN

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique

namespace S143

open A6Model

section PsiA

variable {G : Type*} [Group G] {A : Subgroup G} {e0 e1 e2 e3 : G} (hB : IsBasis A e0 e1 e2 e3)
  {cm : Mat4}

@[expose] noncomputable def psiA (cm : Mat4) (e0 e1 e2 e3 e : G) : N6 :=
  psi cm (coordsOf e0 e1 e2 e3 e)

include hB

theorem psiA_mul {e e' : G} (he : e ∈ A) (he' : e' ∈ A) :
    psiA cm e0 e1 e2 e3 (e * e') = psiA cm e0 e1 e2 e3 e * psiA cm e0 e1 e2 e3 e' := by
  unfold psiA
  rw [hB.coordsOf_mul he he', psi_add]

theorem psiA_one : psiA cm e0 e1 e2 e3 (1 : G) = 1 := by
  unfold psiA
  rw [hB.coordsOf_one]
  show ofCoords (vm V4.zero cm) = 1
  rw [vm_zero]
  simp [ofCoords, V4.zero]

theorem psiA_inv {e : G} (he : e ∈ A) :
    psiA cm e0 e1 e2 e3 e⁻¹ = (psiA cm e0 e1 e2 e3 e)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← psiA_mul hB (A.inv_mem he) he, inv_mul_cancel, psiA_one hB]

theorem psiA_inj (hcm : ∀ v w : V4, vm v cm = vm w cm → v = w) {e e' : G} (he : e ∈ A)
    (he' : e' ∈ A) (h : psiA cm e0 e1 e2 e3 e = psiA cm e0 e1 e2 e3 e') : e = e' :=
  hB.coordsOf_inj he he' (psi_inj hcm h)

theorem psiA_conj {γ : G} (hγ : γ ∈ Subgroup.normalizer (A : Set G)) {e : G} (he : e ∈ A)
    {σ : Equiv.Perm (Fin 6)}
    (hσ : ∀ w : V4, n6Act σ (psi cm w) = psi cm (vm w (cmat e0 e1 e2 e3 γ))) :
    psiA cm e0 e1 e2 e3 (γ * e * γ⁻¹) = n6Act σ (psiA cm e0 e1 e2 e3 e) := by
  unfold psiA
  rw [hB.cmat_spec hγ he, hσ]

theorem psiA_surj (hcm : ∀ v w : V4, vm v cm = vm w cm → v = w) (b : N6) :
    ∃ e ∈ A, psiA cm e0 e1 e2 e3 e = b := by
  obtain ⟨v, hv⟩ := psi_surjective hcm b
  refine ⟨embV e0 e1 e2 e3 v, hB.embV_mem v, ?_⟩
  unfold psiA
  rw [hB.coordsOf_embV, hv]

end PsiA


section Coc

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G} {g : G} {c : Counter T M g}
  {r : G} {hrW : r ∈ Hyp1281Two.wOfU T M} {hrV : r ∉ VZ T M} {hr2 : r * r = 1}
  {x z a r1 : G} (hS : Setup c hrW hrV hr2 x z a r1) {t : G} (htT : t ∈ T)
  (htRQ : t ∉ rOf T M ⊔ qOf T) {y : G} {cm : Mat4} (hM : KModel hS cm y)

@[expose] noncomputable def fcoc (cm : Mat4) (z a r r1 δ : G) (k : ↥(kOf T M (c.Ac hrW hrV hr2))) : N6 :=
  psiA cm z a r r1 ((k : G) * δ * (k : G)⁻¹ * δ⁻¹)

variable {hS}

@[expose] noncomputable def KModel.q (hM : KModel hS cm y) :
    ↥(kOf T M (c.Ac hrW hrV hr2)) →* ↥(alternatingGroup (Fin 6)) :=
  homK hS.basis hM.inj hM.K_le

theorem KModel.q_act (hM : KModel hS cm y) (k : ↥(kOf T M (c.Ac hrW hrV hr2))) (w : V4) :
    n6Act (hM.q k : Equiv.Perm (Fin 6)) (psi cm w) = psi cm (vm w (cmat z a r r1 (k : G))) := by
  show n6Act ((homK hS.basis hM.inj hM.K_le k : ↥(alternatingGroup (Fin 6))) :
    Equiv.Perm (Fin 6)) _ = _
  rw [homK_apply]
  exact (sigmaOfK_spec hS.basis hM.K_le k).2 w

theorem KModel.q_surjective (hM : KModel hS cm y) : Function.Surjective hM.q :=
  homK_surjective hS.basis hM.inj hM.K_le hM.x_K hM.y_K hM.count

include htT htRQ

theorem KModel.q_eq_one_iff (hM : KModel hS cm y) (k : ↥(kOf T M (c.Ac hrW hrV hr2))) :
    hM.q k = 1 ↔ (k : G) ∈ c.Ac hrW hrV hr2 := by
  have hKN := c.kOf_le_normalizer_Ac hrW hrV hr2
  constructor
  · intro h
    have h1 := (homK_eq_one_iff hS.basis hM.inj hM.K_le k).mp h
    have h2 := (hS.basis.cmat_eq_one_iff_mem_centralizer (hKN k.2)).mp h1
    exact hS.kOf_inf_centralizer_le htT htRQ hM ⟨k.2, h2⟩
  · intro h
    apply (homK_eq_one_iff hS.basis hM.inj hM.K_le k).mpr
    exact (hS.basis.cmat_eq_one_iff_mem_centralizer (hKN k.2)).mpr
      (Subgroup.mem_centralizer_iff.mpr fun a' ha' => hS.basis.comm a' ha' k h)

theorem fcoc_mem (hM : KModel hS cm y) {δ : G}
    (hδ : δ ∈ Subgroup.centralizer (c.Ac hrW hrV hr2 : Set G))
    (k : ↥(kOf T M (c.Ac hrW hrV hr2))) :
    (k : G) * δ * (k : G)⁻¹ * δ⁻¹ ∈ c.Ac hrW hrV hr2 :=
  (hS.K_le_commSub htT htRQ hM k.2).2 δ hδ

theorem fcoc_mul (hM : KModel hS cm y) {δ : G}
    (hδ : δ ∈ Subgroup.centralizer (c.Ac hrW hrV hr2 : Set G))
    (k₁ k₂ : ↥(kOf T M (c.Ac hrW hrV hr2))) :
    fcoc cm z a r r1 δ (k₁ * k₂) =
      fcoc cm z a r r1 δ k₁ *
        n6Act (hM.q k₁ : Equiv.Perm (Fin 6))
          (fcoc cm z a r r1 δ k₂) := by
  have hB := hS.basis
  have hKN := c.kOf_le_normalizer_Ac hrW hrV hr2
  have he₁ := fcoc_mem htT htRQ hM hδ k₁
  have he₂ := fcoc_mem htT htRQ hM hδ k₂
  have key : ((k₁ * k₂ : ↥(kOf T M (c.Ac hrW hrV hr2))) : G) * δ *
      ((k₁ * k₂ : ↥(kOf T M (c.Ac hrW hrV hr2))) : G)⁻¹ * δ⁻¹ =
      ((k₁ : G) * ((k₂ : G) * δ * (k₂ : G)⁻¹ * δ⁻¹) * (k₁ : G)⁻¹) *
        ((k₁ : G) * δ * (k₁ : G)⁻¹ * δ⁻¹) := by
    simp only [Subgroup.coe_mul]
    group
  unfold fcoc
  rw [key, psiA_mul hB (conj_mem_of_mem_normalizer (hKN k₁.2) he₂) he₁,
    psiA_conj hB (hKN k₁.2) he₂ (hM.q_act k₁), mul_comm]


omit htT htRQ in
theorem fcoc_of_mem_A (hB : IsBasis (c.Ac hrW hrV hr2) z a r r1) {δ : G}
    (hδ : δ ∈ Subgroup.centralizer (c.Ac hrW hrV hr2 : Set G))
    (k : ↥(kOf T M (c.Ac hrW hrV hr2))) (hk : (k : G) ∈ c.Ac hrW hrV hr2) :
    fcoc cm z a r r1 δ k = 1 := by
  unfold fcoc
  have h : (k : G) * δ * (k : G)⁻¹ * δ⁻¹ = 1 := by
    have h1 := Subgroup.mem_centralizer_iff.mp hδ (k : G) hk
    rw [h1]
    group
  rw [h, psiA_one hB]

theorem fcoc_hom (hM : KModel hS cm y) {δ δ' : G}
    (hδ : δ ∈ Subgroup.centralizer (c.Ac hrW hrV hr2 : Set G))
    (hδ' : δ' ∈ Subgroup.centralizer (c.Ac hrW hrV hr2 : Set G))
    (k : ↥(kOf T M (c.Ac hrW hrV hr2))) :
    fcoc cm z a r r1 (δ * δ') k = fcoc cm z a r r1 δ k * fcoc cm z a r r1 δ' k := by
  have hB := hS.basis
  have he := fcoc_mem htT htRQ hM hδ k
  have he' := fcoc_mem htT htRQ hM hδ' k
  have hδe' : δ * ((k : G) * δ' * (k : G)⁻¹ * δ'⁻¹) * δ⁻¹ =
      (k : G) * δ' * (k : G)⁻¹ * δ'⁻¹ := by
    have h1 := Subgroup.mem_centralizer_iff.mp hδ _ he'
    rw [← h1]
    group
  have key : (k : G) * (δ * δ') * (k : G)⁻¹ * (δ * δ')⁻¹ =
      ((k : G) * δ * (k : G)⁻¹ * δ⁻¹) * (δ * ((k : G) * δ' * (k : G)⁻¹ * δ'⁻¹) * δ⁻¹) := by
    group
  unfold fcoc
  rw [key, hδe', psiA_mul hB he he']

omit htT htRQ in
theorem fcoc_one (hB : IsBasis (c.Ac hrW hrV hr2) z a r r1)
    (k : ↥(kOf T M (c.Ac hrW hrV hr2))) : fcoc cm z a r r1 (1 : G) k = 1 := by
  unfold fcoc
  simp only [mul_one, inv_one, mul_inv_cancel]
  exact psiA_one hB

theorem fcoc_eq_one (hM : KModel hS cm y) {δ : G}
    (hδ : δ ∈ Subgroup.centralizer (c.Ac hrW hrV hr2 : Set G))
    (h : ∀ k : ↥(kOf T M (c.Ac hrW hrV hr2)), fcoc cm z a r r1 δ k = 1) :
    ∀ k ∈ kOf T M (c.Ac hrW hrV hr2), k * δ = δ * k := by
  intro k hk
  have h1 := h ⟨k, hk⟩
  unfold fcoc at h1
  have h2 : k * δ * k⁻¹ * δ⁻¹ = 1 := by
    apply psiA_inj hS.basis hM.inj (fcoc_mem htT htRQ hM hδ ⟨k, hk⟩) (c.Ac hrW hrV hr2).one_mem
    rw [h1, psiA_one hS.basis]
  calc k * δ = (k * δ * k⁻¹ * δ⁻¹) * δ * k := by group
    _ = δ * k := by rw [h2, one_mul]


@[expose] noncomputable def cocyc (hM : KModel hS cm y) (δ : G) : ↥(alternatingGroup (Fin 6)) → N6 :=
  fun σ => fcoc cm z a r r1 δ (Function.surjInv hM.q_surjective σ)

theorem cocyc_q (hM : KModel hS cm y) {δ : G}
    (hδ : δ ∈ Subgroup.centralizer (c.Ac hrW hrV hr2 : Set G))
    (k : ↥(kOf T M (c.Ac hrW hrV hr2))) : cocyc hM δ (hM.q k) = fcoc cm z a r r1 δ k := by
  have hk' := Function.surjInv_eq hM.q_surjective (hM.q k)
  set k' := Function.surjInv hM.q_surjective (hM.q k) with hk'def
  have hA : ((k'⁻¹ * k : ↥(kOf T M (c.Ac hrW hrV hr2))) : G) ∈ c.Ac hrW hrV hr2 :=
    (hM.q_eq_one_iff htT htRQ _).mp (by rw [map_mul, map_inv, hk', inv_mul_cancel])
  have h1 := fcoc_mul htT htRQ hM hδ k' (k'⁻¹ * k)
  rw [fcoc_of_mem_A hS.basis hδ _ hA, map_one, mul_one, mul_inv_cancel_left] at h1
  exact h1.symm

theorem cocyc_isDer (hM : KModel hS cm y) {δ : G}
    (hδ : δ ∈ Subgroup.centralizer (c.Ac hrW hrV hr2 : Set G)) :
    CFSG.Quasithin.B3.IsDer n6ActL (cocyc hM δ) := by
  intro σ σ'
  obtain ⟨k, rfl⟩ := hM.q_surjective σ
  obtain ⟨k', rfl⟩ := hM.q_surjective σ'
  rw [← map_mul, cocyc_q htT htRQ hM hδ, cocyc_q htT htRQ hM hδ, cocyc_q htT htRQ hM hδ,
    fcoc_mul htT htRQ hM hδ]
  rfl

theorem cocyc_mul (hM : KModel hS cm y) {δ δ' : G}
    (hδ : δ ∈ Subgroup.centralizer (c.Ac hrW hrV hr2 : Set G))
    (hδ' : δ' ∈ Subgroup.centralizer (c.Ac hrW hrV hr2 : Set G))
    (σ : ↥(alternatingGroup (Fin 6))) :
    cocyc hM (δ * δ') σ = cocyc hM δ σ * cocyc hM δ' σ := by
  obtain ⟨k, rfl⟩ := hM.q_surjective σ
  rw [cocyc_q htT htRQ hM (Subgroup.mul_mem _ hδ hδ'), cocyc_q htT htRQ hM hδ,
    cocyc_q htT htRQ hM hδ', fcoc_hom htT htRQ hM hδ hδ']

theorem cocyc_injective (hC1 : ∀ γ : G, (∀ k ∈ kOf T M (c.Ac hrW hrV hr2), k * γ = γ * k) → γ = 1)
    (hM : KModel hS cm y) {δ δ' : G}
    (hδ : δ ∈ Subgroup.centralizer (c.Ac hrW hrV hr2 : Set G))
    (hδ' : δ' ∈ Subgroup.centralizer (c.Ac hrW hrV hr2 : Set G))
    (h : cocyc hM δ = cocyc hM δ') : δ = δ' := by
  have hδi : δ⁻¹ ∈ Subgroup.centralizer (c.Ac hrW hrV hr2 : Set G) :=
    (Subgroup.centralizer _).inv_mem hδ
  have hfeq : ∀ k : ↥(kOf T M (c.Ac hrW hrV hr2)),
      fcoc cm z a r r1 δ k = fcoc cm z a r r1 δ' k := fun k => by
    rw [← cocyc_q htT htRQ hM hδ, ← cocyc_q htT htRQ hM hδ', h]
  have hinv : ∀ k : ↥(kOf T M (c.Ac hrW hrV hr2)),
      fcoc cm z a r r1 δ⁻¹ k = (fcoc cm z a r r1 δ k)⁻¹ := fun k => by
    apply eq_inv_of_mul_eq_one_right
    rw [← fcoc_hom htT htRQ hM hδ hδi, mul_inv_cancel, fcoc_one hS.basis]
  have h1 : δ⁻¹ * δ' = 1 := by
    apply hC1
    exact fcoc_eq_one htT htRQ hM (Subgroup.mul_mem _ hδi hδ') (fun k => by
      rw [fcoc_hom htT htRQ hM hδi hδ', hinv, hfeq k, inv_mul_cancel])
  exact inv_mul_eq_one.mp h1

theorem mem_Ac_of_principal (hC1 : ∀ γ : G, (∀ k ∈ kOf T M (c.Ac hrW hrV hr2), k * γ = γ * k) → γ = 1)
    (hM : KModel hS cm y) {δ : G}
    (hδ : δ ∈ Subgroup.centralizer (c.Ac hrW hrV hr2 : Set G)) (b : N6)
    (hb : ∀ σ : ↥(alternatingGroup (Fin 6)), cocyc hM δ σ = n6Act (σ : Equiv.Perm (Fin 6)) b * b⁻¹) :
    δ ∈ c.Ac hrW hrV hr2 := by
  have hB := hS.basis
  have hKN := c.kOf_le_normalizer_Ac hrW hrV hr2
  obtain ⟨a', ha', hψ⟩ := psiA_surj hB hM.inj b
  have hcomm : ∀ k ∈ kOf T M (c.Ac hrW hrV hr2), k * (a'⁻¹ * δ) = (a'⁻¹ * δ) * k := by
    intro k hk
    have hf : fcoc cm z a r r1 δ ⟨k, hk⟩ = psiA cm z a r r1 (k * a' * k⁻¹ * a'⁻¹) := by
      rw [← cocyc_q htT htRQ hM hδ, hb, ← hψ]
      have h1 := psiA_conj hB (hKN hk) ha' (hM.q_act ⟨k, hk⟩)
      have h2 := psiA_mul (cm := cm) hB (conj_mem_of_mem_normalizer (hKN hk) ha') ((c.Ac hrW hrV hr2).inv_mem ha')
      rw [h2, h1, psiA_inv (cm := cm) hB ha']
    have hE : k * δ * k⁻¹ * δ⁻¹ = k * a' * k⁻¹ * a'⁻¹ :=
      psiA_inj hB hM.inj (fcoc_mem htT htRQ hM hδ ⟨k, hk⟩)
        ((c.Ac hrW hrV hr2).mul_mem (conj_mem_of_mem_normalizer (hKN hk) ha')
          ((c.Ac hrW hrV hr2).inv_mem ha')) hf
    have h3 : k * (a'⁻¹ * δ) * k⁻¹ = a'⁻¹ * δ := by
      calc k * (a'⁻¹ * δ) * k⁻¹ = (k * a'⁻¹ * k⁻¹) * (k * δ * k⁻¹ * δ⁻¹) * δ := by group
        _ = (k * a'⁻¹ * k⁻¹) * (k * a' * k⁻¹ * a'⁻¹) * δ := by rw [hE]
        _ = a'⁻¹ * δ := by group
    calc k * (a'⁻¹ * δ) = (k * (a'⁻¹ * δ) * k⁻¹) * k := by group
      _ = (a'⁻¹ * δ) * k := by rw [h3]
  have h4 := hC1 _ hcomm
  have : δ = a' := by
    have := mul_eq_one_iff_eq_inv.mp h4
    simpa using this.symm
  rw [this]
  exact ha'

theorem cocyc_eq_one_of_centralizes (hM : KModel hS cm y) {δ : G}
    (hδ : δ ∈ Subgroup.centralizer (c.Ac hrW hrV hr2 : Set G)) {u : G}
    (hu : u ∈ kOf T M (c.Ac hrW hrV hr2)) (hcu : u * δ = δ * u) :
    cocyc hM δ (hM.q ⟨u, hu⟩) = 1 := by
  rw [cocyc_q htT htRQ hM hδ]
  unfold fcoc
  have : u * δ * u⁻¹ * δ⁻¹ = 1 := by rw [hcu]; group
  show psiA cm z a r r1 (u * δ * u⁻¹ * δ⁻¹) = 1
  rw [this, psiA_one hS.basis]

theorem eq_dW (hM : KModel hS cm y) {δ : G}
    (hδ : δ ∈ Subgroup.centralizer (c.Ac hrW hrV hr2 : Set G)) :
    ∃ w : Fin 6 → ZMod 2, ∀ σ : ↥(alternatingGroup (Fin 6)), cocyc hM δ σ = dW w σ.1 :=
  z1_N6 _ (cocyc_isDer htT htRQ hM hδ)

omit htT htRQ in
theorem cmat_inv_eq_Tz (hB : IsBasis (c.Ac hrW hrV hr2) z a r r1) {d : G}
    (hdN : d ∈ Subgroup.normalizer (c.Ac hrW hrV hr2 : Set G))
    (hD : cmat z a r r1 d = Tz) : cmat z a r r1 d⁻¹ = Tz := by
  have h1 := hB.cmat_mul ((Subgroup.normalizer _).inv_mem hdN) hdN
  rw [inv_mul_cancel, hB.cmat_one, hD] at h1
  calc cmat z a r r1 d⁻¹ = mm I4 (cmat z a r r1 d⁻¹) := (I4_mm _).symm
    _ = mm (mm Tz Tz) (cmat z a r r1 d⁻¹) := by rw [Tz_sq]
    _ = mm Tz (mm Tz (cmat z a r r1 d⁻¹)) := mm_assoc _ _ _
    _ = Tz := by rw [← h1, mm_I4]

omit htT htRQ in
theorem KModel.q_conj (hM : KModel hS cm y) {d : G}
    (hdN : d ∈ Subgroup.normalizer (c.Ac hrW hrV hr2 : Set G))
    (hdK : ∀ k ∈ kOf T M (c.Ac hrW hrV hr2), d * k * d⁻¹ ∈ kOf T M (c.Ac hrW hrV hr2))
    (hD : cmat z a r r1 d = Tz) {s : Equiv.Perm (Fin 6)} (hss : s.sign = -1)
    (hsT : mm cm (matOf6 s) = mm Tz cm) (k : ↥(kOf T M (c.Ac hrW hrV hr2))) :
    (hM.q ⟨d * k * d⁻¹, hdK k k.2⟩ : Equiv.Perm (Fin 6)) = s * (hM.q k : Equiv.Perm (Fin 6)) * s := by
  have hB := hS.basis
  have hKN := c.kOf_le_normalizer_Ac hrW hrV hr2
  have hdi := (Subgroup.normalizer (c.Ac hrW hrV hr2 : Set G)).inv_mem hdN
  have hs' : ∀ w, n6Act s (psi cm w) = psi cm (vm w Tz) := fun w => psi_intertwine hsT w
  have hsign1 : ∀ k' : ↥(kOf T M (c.Ac hrW hrV hr2)), (hM.q k' : Equiv.Perm (Fin 6)).sign = 1 :=
    fun k' => Equiv.Perm.mem_alternatingGroup.mp (hM.q k').2
  refine perm_eq_of_act hM.inj (hsign1 _) ?_ fun w => ?_
  · rw [Equiv.Perm.sign_mul, Equiv.Perm.sign_mul, hsign1 k, hss]
    decide
  · rw [hM.q_act]
    have hc : cmat z a r r1 (d * k * d⁻¹) = mm Tz (mm (cmat z a r r1 (k : G)) Tz) := by
      rw [hB.cmat_mul (Subgroup.mul_mem _ hdN (hKN k.2)) hdi, hB.cmat_mul hdN (hKN k.2),
        cmat_inv_eq_Tz hB hdN hD, hD]
    show psi cm (vm w (cmat z a r r1 (d * k * d⁻¹))) = _
    rw [hc, map_mul, map_mul, MulAut.mul_apply, MulAut.mul_apply, hs', hM.q_act, hs', ← vm_vm,
      ← vm_vm, vm_vm]


theorem fcoc_conj (hM : KModel hS cm y) {δ : G}
    (hδ : δ ∈ Subgroup.centralizer (c.Ac hrW hrV hr2 : Set G)) {d : G}
    (hdN : d ∈ Subgroup.normalizer (c.Ac hrW hrV hr2 : Set G))
    (hdK : ∀ k ∈ kOf T M (c.Ac hrW hrV hr2), d * k * d⁻¹ ∈ kOf T M (c.Ac hrW hrV hr2))
    {s : Equiv.Perm (Fin 6)}
    (hs' : ∀ w, n6Act s (psi cm w) = psi cm (vm w (cmat z a r r1 d))) (hdδ : d * δ = δ * d)
    (k : ↥(kOf T M (c.Ac hrW hrV hr2))) :
    fcoc cm z a r r1 δ ⟨d * k * d⁻¹, hdK k k.2⟩ = n6Act s (fcoc cm z a r r1 δ k) := by
  have hB := hS.basis
  have h1 : d⁻¹ * δ * d = δ := by
    calc d⁻¹ * δ * d = d⁻¹ * (δ * d) := mul_assoc _ _ _
      _ = d⁻¹ * (d * δ) := by rw [hdδ]
      _ = δ := inv_mul_cancel_left _ _
  have h2 : d⁻¹ * δ⁻¹ = δ⁻¹ * d⁻¹ := by
    have := congrArg (·⁻¹) h1
    simp only [mul_inv_rev, inv_inv] at this
    calc d⁻¹ * δ⁻¹ = (d⁻¹ * (δ⁻¹ * d)) * d⁻¹ := by group
      _ = δ⁻¹ * d⁻¹ := by rw [this]
  have e : d * (k : G) * d⁻¹ * δ * (d * (k : G) * d⁻¹)⁻¹ * δ⁻¹ =
      d * ((k : G) * δ * (k : G)⁻¹ * δ⁻¹) * d⁻¹ := by
    calc d * (k : G) * d⁻¹ * δ * (d * (k : G) * d⁻¹)⁻¹ * δ⁻¹
        = d * (k : G) * (d⁻¹ * δ * d) * (k : G)⁻¹ * (d⁻¹ * δ⁻¹) := by group
      _ = d * (k : G) * δ * (k : G)⁻¹ * (δ⁻¹ * d⁻¹) := by rw [h1, h2]
      _ = d * ((k : G) * δ * (k : G)⁻¹ * δ⁻¹) * d⁻¹ := by group
  unfold fcoc
  show psiA cm z a r r1 (d * (k : G) * d⁻¹ * δ * (d * (k : G) * d⁻¹)⁻¹ * δ⁻¹) = _
  rw [e]
  exact psiA_conj hB hdN (fcoc_mem htT htRQ hM hδ k) hs'

theorem cocyc_conj (hM : KModel hS cm y) {δ : G}
    (hδ : δ ∈ Subgroup.centralizer (c.Ac hrW hrV hr2 : Set G)) {d : G}
    (hdN : d ∈ Subgroup.normalizer (c.Ac hrW hrV hr2 : Set G))
    (hdK : ∀ k ∈ kOf T M (c.Ac hrW hrV hr2), d * k * d⁻¹ ∈ kOf T M (c.Ac hrW hrV hr2))
    (hD : cmat z a r r1 d = Tz) {s : Equiv.Perm (Fin 6)} (hss : s.sign = -1)
    (hsT : mm cm (matOf6 s) = mm Tz cm) (hdδ : d * δ = δ * d)
    (σ : ↥(alternatingGroup (Fin 6))) (hmem : s * (σ : Equiv.Perm (Fin 6)) * s ∈ alternatingGroup (Fin 6)) :
    cocyc hM δ ⟨s * (σ : Equiv.Perm (Fin 6)) * s, hmem⟩ = n6Act s (cocyc hM δ σ) := by
  obtain ⟨k, rfl⟩ := hM.q_surjective σ
  have hq := KModel.q_conj hM hdN hdK hD hss hsT k
  have e : (⟨s * (hM.q k : Equiv.Perm (Fin 6)) * s, hmem⟩ : ↥(alternatingGroup (Fin 6))) =
      hM.q ⟨d * k * d⁻¹, hdK k k.2⟩ := Subtype.ext hq.symm
  rw [e, cocyc_q htT htRQ hM hδ, cocyc_q htT htRQ hM hδ]
  exact fcoc_conj htT htRQ hM hδ hdN hdK (fun w => by rw [hD]; exact psi_intertwine hsT w) hdδ k

end Coc


end S143

end CFSG.Quasithin
