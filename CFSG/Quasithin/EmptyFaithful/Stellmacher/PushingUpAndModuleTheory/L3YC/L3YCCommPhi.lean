module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.L3YC.L3YCBilZero

public section

namespace CFSG.Quasithin

namespace Stellmacher.PU.L3YC

section Proj

variable {G : Type} [Group G]

theorem mem_sup_of_commute {A B : Subgroup G} (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {x : G}
    (hx : x ∈ A ⊔ B) : ∃ a ∈ A, ∃ b ∈ B, x = a * b := by
  let S : Subgroup G :=
    { carrier := {x | ∃ a ∈ A, ∃ b ∈ B, x = a * b}
      one_mem' := ⟨1, A.one_mem, 1, B.one_mem, by simp⟩
      mul_mem' := by
        rintro _ _ ⟨a, ha, b, hb, rfl⟩ ⟨a', ha', b', hb', rfl⟩
        refine ⟨a * a', A.mul_mem ha ha', b * b', B.mul_mem hb hb', ?_⟩
        calc a * b * (a' * b') = a * (b * a') * b' := by group
          _ = a * (a' * b) * b' := by rw [← hc a' ha' b hb]
          _ = a * a' * (b * b') := by group
      inv_mem' := by
        rintro _ ⟨a, ha, b, hb, rfl⟩
        refine ⟨a⁻¹, A.inv_mem ha, b⁻¹, B.inv_mem hb, ?_⟩
        calc (a * b)⁻¹ = b⁻¹ * a⁻¹ := by group
          _ = a⁻¹ * b⁻¹ := by
            have := hc a⁻¹ (A.inv_mem ha) b⁻¹ (B.inv_mem hb)
            exact this.symm }
  have : A ⊔ B ≤ S := sup_le (fun a ha => ⟨a, ha, 1, B.one_mem, by simp⟩)
    (fun b hb => ⟨1, A.one_mem, b, hb, by simp⟩)
  exact this hx

theorem exists_proj {C U Z : Subgroup G} (hZ : Z = C ⊔ U) (hCU : C ⊓ U = ⊥)
    (hc : ∀ a ∈ C, ∀ b ∈ U, a * b = b * a) :
    ∃ π : ↥Z →* ↥U, ∀ z : ↥Z, ∃ c ∈ C, (z : G) = c * (π z : G) := by
  classical
  have hdec : ∀ z : ↥Z, ∃ c ∈ C, ∃ u ∈ U, (z : G) = c * u := fun z =>
    mem_sup_of_commute hc (hZ ▸ z.2)
  have huniq : ∀ c c' : G, c ∈ C → c' ∈ C → ∀ u u' : G, u ∈ U → u' ∈ U → c * u = c' * u' →
      u = u' := by
    intro c c' hcC hc'C u u' hu hu' h
    have h1 : c'⁻¹ * c = u' * u⁻¹ := by
      calc c'⁻¹ * c = c'⁻¹ * (c * u) * u⁻¹ := by group
        _ = c'⁻¹ * (c' * u') * u⁻¹ := by rw [h]
        _ = u' * u⁻¹ := by group
    have hmem : u' * u⁻¹ ∈ C ⊓ U :=
      ⟨h1 ▸ C.mul_mem (C.inv_mem hc'C) hcC, U.mul_mem hu' (U.inv_mem hu)⟩
    rw [hCU, Subgroup.mem_bot] at hmem
    calc u = (u' * u⁻¹)⁻¹ * u' := by group
      _ = u' := by rw [hmem]; group
  let f : ↥Z → ↥U := fun z => ⟨(hdec z).choose_spec.2.choose, (hdec z).choose_spec.2.choose_spec.1⟩
  have hf : ∀ z : ↥Z, (z : G) = (hdec z).choose * (f z : G) := fun z =>
    (hdec z).choose_spec.2.choose_spec.2
  refine ⟨{ toFun := f, map_one' := ?_, map_mul' := ?_ }, fun z => ⟨_, (hdec z).choose_spec.1, hf z⟩⟩
  · apply Subtype.ext
    have := huniq (hdec 1).choose 1 (hdec 1).choose_spec.1 C.one_mem (f 1 : G) 1 (f 1).2 U.one_mem
      (by rw [← hf 1]; simp)
    exact this
  · intro z z'
    apply Subtype.ext
    obtain ⟨c, hcC, hcz⟩ : ∃ c ∈ C, (z : G) = c * (f z : G) :=
      ⟨_, (hdec z).choose_spec.1, hf z⟩
    obtain ⟨c', hcC', hcz'⟩ : ∃ c ∈ C, (z' : G) = c * (f z' : G) :=
      ⟨_, (hdec z').choose_spec.1, hf z'⟩
    obtain ⟨c'', hcC'', hcz''⟩ : ∃ c ∈ C, ((z * z' : ↥Z) : G) = c * (f (z * z') : G) :=
      ⟨_, (hdec (z * z')).choose_spec.1, hf (z * z')⟩
    have hprod : ((z * z' : ↥Z) : G) = (c * c') * ((f z : G) * (f z' : G)) := by
      show (z : G) * (z' : G) = _
      rw [hcz, hcz']
      calc c * (f z : G) * (c' * (f z' : G)) = c * ((f z : G) * c') * (f z' : G) := by group
        _ = c * (c' * (f z : G)) * (f z' : G) := by rw [← hc c' hcC' _ (f z).2]
        _ = c * c' * ((f z : G) * (f z' : G)) := by group
    exact huniq c'' (c * c') hcC'' (C.mul_mem hcC hcC') _ _ (f (z * z')).2
      (U.mul_mem (f z).2 (f z').2) (by rw [← hcz'', hprod]; rfl)

theorem comm_mem_of_trivial {L Φ Z Q : Subgroup G} {F : Type} [Field F]
    {α : ↥L →* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F)} {dual : Bool}
    (hnat : IsSumOfNaturalModulesVia L Φ Z α dual 1)
    (hQtriv : ∀ q ∈ Q, ∃ l : ↥L, (l : G) = q ∧ α l = 1) {q φ : G} (hq : q ∈ Q) (hφ : φ ∈ Φ) :
    q * φ * q⁻¹ * φ⁻¹ ∈ Z := by
  obtain ⟨hLN, -, β, -, hβk, hβe⟩ := hnat
  obtain ⟨l, hl, hα1⟩ := hQtriv q hq
  have hmem : q * φ * q⁻¹ ∈ Φ := by
    have := (Subgroup.mem_normalizer_iff.mp (hLN l.2) φ).mp hφ
    rwa [hl] at this
  have hb := hβe l ⟨φ, hφ⟩ ⟨q * φ * q⁻¹, hmem⟩ (by simp [hl]) 0
  rw [hα1] at hb
  have hone : moduleAct dual (((1 : ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F)) :
      Matrix.GeneralLinearGroup (Fin 3) F)) = 1 := by
    cases dual <;> simp [moduleAct]
  rw [hone, Matrix.one_mulVec] at hb
  have hbb : β ⟨q * φ * q⁻¹, hmem⟩ = β ⟨φ, hφ⟩ := by
    apply Multiplicative.toAdd.injective
    funext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst hi
    exact hb
  have hker : (⟨q * φ * q⁻¹, hmem⟩ : ↥Φ) * ⟨φ, hφ⟩⁻¹ ∈ β.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hbb, mul_inv_cancel]
  rw [hβk, Subgroup.mem_subgroupOf] at hker
  simpa using hker

theorem proj_unique {C U : Subgroup G} (hCU : C ⊓ U = ⊥) {c c' u u' : G} (hc : c ∈ C) (hc' : c' ∈ C)
    (hu : u ∈ U) (hu' : u' ∈ U) (h : c * u = c' * u') : u = u' := by
  have h1 : c'⁻¹ * c = u' * u⁻¹ := by
    calc c'⁻¹ * c = c'⁻¹ * (c * u) * u⁻¹ := by group
      _ = c'⁻¹ * (c' * u') * u⁻¹ := by rw [h]
      _ = u' * u⁻¹ := by group
  have hmem : u' * u⁻¹ ∈ C ⊓ U := ⟨h1 ▸ C.mul_mem (C.inv_mem hc') hc, U.mul_mem hu' (U.inv_mem hu)⟩
  rw [hCU, Subgroup.mem_bot] at hmem
  calc u = (u' * u⁻¹)⁻¹ * u' := by group
    _ = u' := by rw [hmem]; group

end Proj

section CommLem

variable {G : Type} [Group G]

theorem comm_mul_left' {Q Z : Subgroup G} (hZQ : Z ≤ Q) (hZc : ∀ z ∈ Z, ∀ q ∈ Q, z * q = q * z)
    {q q' φ : G} (hq : q ∈ Q) (hx : q * φ * q⁻¹ * φ⁻¹ ∈ Z) (hy : q' * φ * q'⁻¹ * φ⁻¹ ∈ Z) :
    (q * q') * φ * (q * q')⁻¹ * φ⁻¹ = (q * φ * q⁻¹ * φ⁻¹) * (q' * φ * q'⁻¹ * φ⁻¹) := by
  have h1 := hZc _ hy q hq
  have h2 := hZc _ hx _ (hZQ hy)
  calc (q * q') * φ * (q * q')⁻¹ * φ⁻¹
      = q * (q' * φ * q'⁻¹ * φ⁻¹) * φ * q⁻¹ * φ⁻¹ := by group
    _ = (q' * φ * q'⁻¹ * φ⁻¹) * q * φ * q⁻¹ * φ⁻¹ := by rw [← h1]
    _ = (q' * φ * q'⁻¹ * φ⁻¹) * (q * φ * q⁻¹ * φ⁻¹) := by group
    _ = _ := h2.symm

end CommLem

section Main

open Matrix

variable {G : Type} [Group G]

open CFSG.Assembly.LowTwoRank (StatedSL)

theorem commutator_values_in_C
    {L Q Φ Z K C U : Subgroup G} {F : Type} [Field F] [Fintype F] (hF : Fintype.card F = 2)
    (α : ↥L →* ↥(StatedSL 3 F)) (hα : Function.Surjective α)
    (hΦQ : Φ ≤ Q) (hZQ : Z ≤ Q) (hZc : ∀ z ∈ Z, ∀ q ∈ Q, z * q = q * z)
    (hKQ : K ≤ Q) (hKdef : ∀ k ∈ K, ∀ φ ∈ Φ, k * φ = φ * k)
    (hQtriv : ∀ q ∈ Q, ∃ l : ↥L, (l : G) = q ∧ α l = 1)
    (hnatQ : IsSumOfNaturalModulesVia L Q K α false 2)
    (hnatΦ : IsSumOfNaturalModulesVia L Φ Z α true 1)
    (hnatU : IsSumOfNaturalModulesVia L U ⊥ α false 1)
    (hZ : Z = C ⊔ U) (hCU : C ⊓ U = ⊥) (hCL : ∀ l ∈ L, ∀ c ∈ C, l * c * l⁻¹ = c)
    {q φ : G} (hq : q ∈ Q) (hφ : φ ∈ Φ) : q * φ * q⁻¹ * φ⁻¹ ∈ C := by
  classical
  have hCZ : C ≤ Z := hZ ▸ le_sup_left
  have hUZ : U ≤ Z := hZ ▸ le_sup_right
  obtain ⟨π, hπ⟩ := exists_proj hZ hCU
    (fun a ha b hb => hZc a (hCZ ha) b (hZQ (hUZ hb)))
  have hcomZ : ∀ q ∈ Q, ∀ φ ∈ Φ, q * φ * q⁻¹ * φ⁻¹ ∈ Z := fun q hq φ hφ =>
    comm_mem_of_trivial hnatΦ hQtriv hq hφ
  obtain ⟨hLNU, -, βU, hβUs, hβUk, hβUe⟩ := hnatU
  obtain ⟨hLNQ, -, βQ, hβQs, hβQk, hβQe⟩ := hnatQ
  obtain ⟨hLNΦ, -, βΦ, hβΦs, hβΦk, hβΦe⟩ := hnatΦ
  let T : ↥Q → ↥Φ → ↥Z := fun q φ => ⟨q * φ * q⁻¹ * φ⁻¹, hcomZ q q.2 φ φ.2⟩
  let cU : ↥U → (Fin 3 → F) := fun u => Multiplicative.toAdd (βU u) 0
  have hcU_add : ∀ u u' : ↥U, cU (u * u') = cU u + cU u' := fun u u' => by
    simp [cU]
  have hcU_one : cU 1 = 0 := by simp [cU]
  have hcU_inj : ∀ u : ↥U, cU u = 0 → u = 1 := by
    intro u hu
    have h1 : βU u = 1 := by
      apply Multiplicative.toAdd.injective
      funext i
      have hi : i = 0 := Subsingleton.elim _ _
      subst hi
      simpa [cU] using hu
    have h2 : u ∈ βU.ker := h1
    rw [hβUk, Subgroup.mem_subgroupOf] at h2
    exact Subtype.ext (by simpa using h2)
  have hZabel : ∀ z z' : ↥Z, z * z' = z' * z := fun z z' =>
    Subtype.ext (hZc z z.2 z' (hZQ z'.2))
  have hT_left : ∀ (q q' : ↥Q) (φ : ↥Φ), T (q * q') φ = T q φ * T q' φ := by
    intro q q' φ
    apply Subtype.ext
    have hy := hZc _ (T q' φ).2 q q.2
    have e1 : ((q * q' : ↥Q) : G) * (φ : G) * ((q * q' : ↥Q) : G)⁻¹ * (φ : G)⁻¹ =
        (q : G) * ((q' : G) * φ * (q' : G)⁻¹ * (φ : G)⁻¹) * (φ : G) * (q : G)⁻¹ * (φ : G)⁻¹ := by
      simp only [Subgroup.coe_mul, InvMemClass.coe_inv]; group
    have e2 : (q : G) * ((q' : G) * φ * (q' : G)⁻¹ * (φ : G)⁻¹) =
        ((q' : G) * φ * (q' : G)⁻¹ * (φ : G)⁻¹) * (q : G) := hy.symm
    show ((q * q' : ↥Q) : G) * (φ : G) * ((q * q' : ↥Q) : G)⁻¹ * (φ : G)⁻¹ =
      (q : G) * φ * (q : G)⁻¹ * (φ : G)⁻¹ * ((q' : G) * φ * (q' : G)⁻¹ * (φ : G)⁻¹)
    have hc := congrArg Subtype.val (hZabel (T q φ) (T q' φ))
    simp only [Subgroup.coe_mul] at hc
    rw [e1, e2]
    calc ((q' : G) * φ * (q' : G)⁻¹ * (φ : G)⁻¹) * (q : G) * (φ : G) * (q : G)⁻¹ * (φ : G)⁻¹
        = ((q' : G) * φ * (q' : G)⁻¹ * (φ : G)⁻¹) * ((q : G) * φ * (q : G)⁻¹ * (φ : G)⁻¹) := by
          group
      _ = _ := hc.symm
  have hT_right : ∀ (q : ↥Q) (φ φ' : ↥Φ), T q (φ * φ') = T q φ * T q φ' := by
    intro q φ φ'
    apply Subtype.ext
    have hx' := hZc _ (T q φ').2 (φ : G) (hΦQ φ.2)
    show (q : G) * ((φ * φ' : ↥Φ) : G) * (q : G)⁻¹ * ((φ * φ' : ↥Φ) : G)⁻¹ =
      (q : G) * φ * (q : G)⁻¹ * (φ : G)⁻¹ * ((q : G) * φ' * (q : G)⁻¹ * (φ' : G)⁻¹)
    simp only [Subgroup.coe_mul]
    have e1 : (q : G) * ((φ : G) * (φ' : G)) * (q : G)⁻¹ * ((φ : G) * (φ' : G))⁻¹ =
        ((q : G) * φ * (q : G)⁻¹ * (φ : G)⁻¹) *
          ((φ : G) * ((q : G) * φ' * (q : G)⁻¹ * (φ' : G)⁻¹) * (φ : G)⁻¹) := by group
    rw [e1]
    congr 1
    have hx'' : ((q : G) * φ' * (q : G)⁻¹ * (φ' : G)⁻¹) * (φ : G) =
        (φ : G) * ((q : G) * φ' * (q : G)⁻¹ * (φ' : G)⁻¹) := hx'
    calc (φ : G) * ((q : G) * φ' * (q : G)⁻¹ * (φ' : G)⁻¹) * (φ : G)⁻¹
        = (((q : G) * φ' * (q : G)⁻¹ * (φ' : G)⁻¹) * (φ : G)) * (φ : G)⁻¹ := by rw [hx'']
      _ = _ := by group
  have hT_K : ∀ (q : ↥Q) (φ : ↥Φ), (q : G) ∈ K → T q φ = 1 := by
    intro q φ hqK
    apply Subtype.ext
    have := hKdef q hqK φ φ.2
    show (q : G) * φ * (q : G)⁻¹ * (φ : G)⁻¹ = 1
    rw [this]; group
  have hT_Z : ∀ (q : ↥Q) (φ : ↥Φ), (φ : G) ∈ Z → T q φ = 1 := by
    intro q φ hφZ
    apply Subtype.ext
    have := hZc φ hφZ q q.2
    show (q : G) * φ * (q : G)⁻¹ * (φ : G)⁻¹ = 1
    rw [← this]; group
  let Θ : ↥Q → ↥Φ → (Fin 3 → F) := fun q φ => cU (π (T q φ))
  have hΘ_left : ∀ (q q' : ↥Q) (φ : ↥Φ), Θ (q * q') φ = Θ q φ + Θ q' φ := by
    intro q q' φ
    simp only [Θ, hT_left, map_mul, hcU_add]
  have hΘ_right : ∀ (q : ↥Q) (φ φ' : ↥Φ), Θ q (φ * φ') = Θ q φ + Θ q φ' := by
    intro q φ φ'
    simp only [Θ, hT_right, map_mul, hcU_add]
  have hΘ_K : ∀ (q : ↥Q) (φ : ↥Φ), (q : G) ∈ K → Θ q φ = 0 := by
    intro q φ h
    simp only [Θ, hT_K q φ h, map_one, hcU_one]
  have hΘ_Z : ∀ (q : ↥Q) (φ : ↥Φ), (φ : G) ∈ Z → Θ q φ = 0 := by
    intro q φ h
    simp only [Θ, hT_Z q φ h, map_one, hcU_one]
  have hΘ_congr : ∀ (q q' : ↥Q) (φ φ' : ↥Φ), βQ q = βQ q' → βΦ φ = βΦ φ' →
      Θ q φ = Θ q' φ' := by
    intro q q' φ φ' hq hφ
    have hk : (q⁻¹ * q' : ↥Q) ∈ βQ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hq, inv_mul_cancel]
    rw [hβQk, Subgroup.mem_subgroupOf] at hk
    have hz : (φ⁻¹ * φ' : ↥Φ) ∈ βΦ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hφ, inv_mul_cancel]
    rw [hβΦk, Subgroup.mem_subgroupOf] at hz
    have e1 : q' = q * (q⁻¹ * q') := by group
    have e2 : φ' = φ * (φ⁻¹ * φ') := by group
    rw [e1, e2, hΘ_left, hΘ_right, hΘ_K (q⁻¹ * q') _ (by simpa using hk), hΘ_Z _ (φ⁻¹ * φ') (by simpa using hz)]
    simp [hΘ_K (q⁻¹ * q') φ (by simpa using hk)]
  let conjQ : ↥L → ↥Q → ↥Q := fun l q =>
    ⟨(l : G) * q * (l : G)⁻¹, (Subgroup.mem_normalizer_iff.mp (hLNQ l.2) q).mp q.2⟩
  let conjΦ : ↥L → ↥Φ → ↥Φ := fun l φ =>
    ⟨(l : G) * φ * (l : G)⁻¹, (Subgroup.mem_normalizer_iff.mp (hLNΦ l.2) φ).mp φ.2⟩
  have hπ_conj : ∀ (l : ↥L) (z z' : ↥Z), (z' : G) = l * z * l⁻¹ →
      ((π z' : ↥U) : G) = l * (π z : G) * l⁻¹ := by
    intro l z z' h
    obtain ⟨c, hc, hcz⟩ := hπ z
    obtain ⟨c', hc', hcz'⟩ := hπ z'
    have hU : (l : G) * (π z : G) * (l : G)⁻¹ ∈ U :=
      (Subgroup.mem_normalizer_iff.mp (hLNU l.2) _).mp (π z).2
    refine proj_unique hCU hc' hc (π z').2 hU ?_
    calc c' * ((π z' : ↥U) : G) = (z' : G) := hcz'.symm
      _ = (l : G) * z * (l : G)⁻¹ := h
      _ = (l : G) * (c * ((π z : ↥U) : G)) * (l : G)⁻¹ := by rw [← hcz]
      _ = ((l : G) * c * (l : G)⁻¹) * ((l : G) * (π z : G) * (l : G)⁻¹) := by group
      _ = c * ((l : G) * (π z : G) * (l : G)⁻¹) := by rw [hCL l l.2 c hc]
  have hΘ_conj : ∀ (l : ↥L) (q : ↥Q) (φ : ↥Φ),
      Θ (conjQ l q) (conjΦ l φ) =
        ((α l : Matrix.GeneralLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).mulVec (Θ q φ) := by
    intro l q φ
    have hT : ((T (conjQ l q) (conjΦ l φ) : ↥Z) : G) = (l : G) * (T q φ : G) * (l : G)⁻¹ := by
      show (l : G) * q * (l : G)⁻¹ * ((l : G) * φ * (l : G)⁻¹) * ((l : G) * q * (l : G)⁻¹)⁻¹ *
        ((l : G) * φ * (l : G)⁻¹)⁻¹ = (l : G) * ((q : G) * φ * (q : G)⁻¹ * (φ : G)⁻¹) * (l : G)⁻¹
      group
    have h1 := hπ_conj l (T q φ) (T (conjQ l q) (conjΦ l φ)) hT
    have h2 := hβUe l (π (T q φ)) (π (T (conjQ l q) (conjΦ l φ))) h1 0
    simpa [Θ, cU, moduleAct] using h2
  let sQ : Multiplicative (Fin 2 → Fin 3 → F) → ↥Q := Function.surjInv hβQs
  let sΦ : Multiplicative (Fin 1 → Fin 3 → F) → ↥Φ := Function.surjInv hβΦs
  have hsQ : ∀ m, βQ (sQ m) = m := Function.surjInv_eq hβQs
  have hsΦ : ∀ m, βΦ (sΦ m) = m := Function.surjInv_eq hβΦs
  let B : (Fin 2 → Fin 3 → F) → (Fin 3 → F) → (Fin 3 → F) := fun x y =>
    Θ (sQ (Multiplicative.ofAdd x)) (sΦ (Multiplicative.ofAdd (fun _ => y)))
  have hfun1 : ∀ g : Fin 1 → Fin 3 → F, (fun _ : Fin 1 => g 0) = g := by
    intro g; funext i; have : i = 0 := Subsingleton.elim _ _; subst this; rfl
  have hB_eval : ∀ (q : ↥Q) (φ : ↥Φ),
      B (Multiplicative.toAdd (βQ q)) (Multiplicative.toAdd (βΦ φ) 0) = Θ q φ := by
    intro q φ
    apply hΘ_congr
    · rw [hsQ]; rfl
    · rw [hsΦ, hfun1]; rfl
  have hB_addL : ∀ x x' y, B (x + x') y = B x y + B x' y := by
    intro x x' y
    have : Θ (sQ (Multiplicative.ofAdd (x + x'))) (sΦ (Multiplicative.ofAdd (fun _ => y))) =
        Θ (sQ (Multiplicative.ofAdd x) * sQ (Multiplicative.ofAdd x'))
          (sΦ (Multiplicative.ofAdd (fun _ => y))) := by
      apply hΘ_congr
      · rw [map_mul, hsQ, hsQ, hsQ]; rfl
      · rfl
    simp only [B]
    rw [this, hΘ_left]
  have hB_addR : ∀ x y y', B x (y + y') = B x y + B x y' := by
    intro x y y'
    have : Θ (sQ (Multiplicative.ofAdd x)) (sΦ (Multiplicative.ofAdd (fun _ => y + y'))) =
        Θ (sQ (Multiplicative.ofAdd x))
          (sΦ (Multiplicative.ofAdd (fun _ => y)) * sΦ (Multiplicative.ofAdd (fun _ => y'))) := by
      apply hΘ_congr
      · rfl
      · rw [map_mul, hsΦ, hsΦ, hsΦ]; rfl
    simp only [B]
    rw [this, hΘ_right]
  let Bi : Fin 2 → (Fin 3 → F) →+ (Fin 3 → F) →+ (Fin 3 → F) := fun i =>
    AddMonoidHom.mk' (fun x => AddMonoidHom.mk' (fun y => B (Pi.single i x) y)
      (fun y y' => hB_addR _ y y'))
      (fun x x' => by
        refine AddMonoidHom.ext fun y => ?_
        show B (Pi.single i (x + x')) y = B (Pi.single i x) y + B (Pi.single i x') y
        rw [Pi.single_add, hB_addL])
  have hBi : ∀ (i : Fin 2) (g : Matrix.GeneralLinearGroup (Fin 3) F) (x y : Fin 3 → F),
      Bi i ((g : Matrix (Fin 3) (Fin 3) F).mulVec x)
        (((g⁻¹ : Matrix.GeneralLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)ᵀ.mulVec y) =
        (g : Matrix (Fin 3) (Fin 3) F).mulVec (Bi i x y) := by
    intro i g x y
    have hg : g ∈ StatedSL 3 F := by
      rw [statedSL_eq_top_of_card_two hF]; trivial
    obtain ⟨l, hl⟩ := hα ⟨g, hg⟩
    have hlg : ((α l : ↥(StatedSL 3 F)) : Matrix.GeneralLinearGroup (Fin 3) F) = g := by
      rw [hl]
    set q0 : ↥Q := sQ (Multiplicative.ofAdd (Pi.single i x)) with hq0
    set φ0 : ↥Φ := sΦ (Multiplicative.ofAdd (fun _ => y)) with hφ0
    have hq0β : Multiplicative.toAdd (βQ q0) = Pi.single i x := by rw [hq0, hsQ]; rfl
    have hφ0β : Multiplicative.toAdd (βΦ φ0) 0 = y := by rw [hφ0, hsΦ]; rfl
    have hc1 : βQ (conjQ l q0) = Multiplicative.ofAdd (Pi.single i
        ((g : Matrix (Fin 3) (Fin 3) F).mulVec x)) := by
      apply Multiplicative.toAdd.injective
      funext j
      have := hβQe l q0 (conjQ l q0) rfl j
      rw [this, hq0β, hlg]
      by_cases hj : j = i
      · subst hj; simp [moduleAct]
      · simp [moduleAct, Pi.single_apply, hj]
    have hc2 : βΦ (conjΦ l φ0) = Multiplicative.ofAdd (fun _ => (((g⁻¹ : Matrix.GeneralLinearGroup
        (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)ᵀ).mulVec y) := by
      apply Multiplicative.toAdd.injective
      funext j
      have hj : j = 0 := Subsingleton.elim _ _
      subst hj
      have := hβΦe l φ0 (conjΦ l φ0) rfl 0
      rw [this, hφ0β, hlg]
      simp [moduleAct]
    have e1 : Bi i ((g : Matrix (Fin 3) (Fin 3) F).mulVec x)
        (((g⁻¹ : Matrix.GeneralLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)ᵀ.mulVec y) =
        Θ (conjQ l q0) (conjΦ l φ0) := by
      show B (Pi.single i ((g : Matrix (Fin 3) (Fin 3) F).mulVec x)) _ = _
      apply hΘ_congr
      · rw [hsQ, hc1]
      · rw [hsΦ, hc2]
    have e2 : Bi i x y = Θ q0 φ0 := by
      show B (Pi.single i x) y = _
      rfl
    rw [e1, e2, hΘ_conj, hlg]
  have hB0 : ∀ (i : Fin 2) (x y : Fin 3 → F), B (Pi.single i x) y = 0 := fun i x y =>
    bil_zero hF (Bi i) (hBi i) x y
  have hBx : ∀ (x : Fin 2 → Fin 3 → F) (y : Fin 3 → F), B x y = 0 := by
    intro x y
    let Bxy : (Fin 2 → Fin 3 → F) →+ (Fin 3 → F) :=
      AddMonoidHom.mk' (fun x => B x y) (fun a b => hB_addL a b y)
    have hx : x = ∑ i, Pi.single i (x i) := (Finset.univ_sum_single x).symm
    show Bxy x = 0
    rw [hx, map_sum]
    exact Finset.sum_eq_zero fun i _ => hB0 i (x i) y
  have hΘ0 : Θ ⟨q, hq⟩ ⟨φ, hφ⟩ = 0 := by
    rw [← hB_eval]; exact hBx _ _
  have hπ1 : π (T ⟨q, hq⟩ ⟨φ, hφ⟩) = 1 := hcU_inj _ hΘ0
  obtain ⟨c, hcC, hcz⟩ := hπ (T ⟨q, hq⟩ ⟨φ, hφ⟩)
  rw [hπ1] at hcz
  have h2 : ((T ⟨q, hq⟩ ⟨φ, hφ⟩ : ↥Z) : G) = c := by simpa using hcz
  have h3 : q * φ * q⁻¹ * φ⁻¹ = c := h2
  rw [h3]; exact hcC

open Matrix in
theorem comm_frattini_eq [Finite G]
    {L Q Φ Z K C U : Subgroup G} {F : Type} [Field F] [Fintype F] (hF : Fintype.card F = 2)
    (α : ↥L →* ↥(StatedSL 3 F)) (hα : Function.Surjective α)
    (hΦQ : Φ ≤ Q) (hZQ : Z ≤ Q) (hZc : ∀ z ∈ Z, ∀ q ∈ Q, z * q = q * z)
    (hKQ : K ≤ Q) (hKdef : ∀ k ∈ K, ∀ φ ∈ Φ, k * φ = φ * k)
    (hKdef' : ∀ q ∈ Q, (∀ φ ∈ Φ, q * φ = φ * q) → q ∈ K)
    (hQtriv : ∀ q ∈ Q, ∃ l : ↥L, (l : G) = q ∧ α l = 1)
    (hnatQ : IsSumOfNaturalModulesVia L Q K α false 2)
    (hnatΦ : IsSumOfNaturalModulesVia L Φ Z α true 1)
    (hnatU : IsSumOfNaturalModulesVia L U ⊥ α false 1)
    (hZ : Z = C ⊔ U) (hCU : C ⊓ U = ⊥) (hCL : ∀ l ∈ L, ∀ c ∈ C, l * c * l⁻¹ = c)
    (hC4 : Nat.card C = 4) : ⁅Q, Φ⁆ = C := by
  classical
  have hle : ⁅Q, Φ⁆ ≤ C := Subgroup.commutator_le.mpr fun q hq φ hφ =>
    commutator_values_in_C hF α hα hΦQ hZQ hZc hKQ hKdef hQtriv hnatQ hnatΦ hnatU hZ hCU hCL hq hφ
  have hcomZ : ∀ q ∈ Q, ∀ φ ∈ Φ, q * φ * q⁻¹ * φ⁻¹ ∈ Z := fun q hq φ hφ =>
    comm_mem_of_trivial hnatΦ hQtriv hq hφ
  obtain ⟨hLNQ, -, βQ, hβQs, hβQk, hβQe⟩ := hnatQ
  obtain ⟨hLNΦ, -, βΦ, hβΦs, hβΦk, hβΦe⟩ := hnatΦ
  let W : Subgroup G := ⁅Q, Φ⁆
  let c : ↥Q → ↥Φ → ↥W := fun q φ => ⟨q * φ * q⁻¹ * φ⁻¹, Subgroup.commutator_mem_commutator q.2 φ.2⟩
  have hcomm_all : ∀ (q' : ↥Q) (φk : Fin 3 → ↥Φ),
      (∀ k, Multiplicative.toAdd (βΦ (φk k)) 0 = Pi.single k 1) →
      (∀ k, (q' : G) * φk k = φk k * q') → ∀ φ ∈ Φ, (q' : G) * φ = φ * q' := by
    intro q' φk hφk hcm φ hφ
    let Pw : (Fin 3 → F) → Prop := fun y =>
      ∃ ψ : ↥Φ, Multiplicative.toAdd (βΦ ψ) 0 = y ∧ (q' : G) * ψ = ψ * q'
    have hPw0 : Pw 0 := ⟨1, by simp, by simp⟩
    have hPwadd : ∀ y y', Pw y → Pw y' → Pw (y + y') := by
      rintro y y' ⟨ψ, h1, h2⟩ ⟨ψ', h1', h2'⟩
      refine ⟨ψ * ψ', by simp [h1, h1'], ?_⟩
      show (q' : G) * ((ψ : G) * ψ') = (ψ : G) * ψ' * q'
      rw [← mul_assoc, h2, mul_assoc, h2', mul_assoc]
    have hPwk : ∀ k (a : F), (a = 0 ∨ a = 1) → Pw (Pi.single k a) := by
      intro k a ha
      rcases ha with rfl | rfl
      · simpa using hPw0
      · exact ⟨φk k, hφk k, hcm k⟩
    have hPwall : ∀ y, Pw y := by
      intro y
      rw [← Finset.univ_sum_single y]
      refine Finset.sum_induction _ Pw hPwadd hPw0 fun k _ => ?_
      exact hPwk k (y k) (eq_zero_or_one_of_card_two hF _)
    obtain ⟨ψ, hψ, hψc⟩ := hPwall (Multiplicative.toAdd (βΦ ⟨φ, hφ⟩) 0)
    have hβ : βΦ ψ = βΦ ⟨φ, hφ⟩ := by
      apply Multiplicative.toAdd.injective
      funext i
      have hi : i = 0 := Subsingleton.elim _ _
      subst hi
      exact hψ
    have hker : ψ⁻¹ * ⟨φ, hφ⟩ ∈ βΦ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hβ, inv_mul_cancel]
    rw [hβΦk, Subgroup.mem_subgroupOf] at hker
    have hz : ((ψ⁻¹ * ⟨φ, hφ⟩ : ↥Φ) : G) ∈ Z := hker
    have hcz := hZc _ hz q' q'.2
    have e : φ = (ψ : G) * (((ψ⁻¹ * ⟨φ, hφ⟩ : ↥Φ)) : G) := by simp
    rw [e, ← mul_assoc, hψc, mul_assoc, mul_assoc]
    congr 1
    exact hcz.symm
  let sQ : Multiplicative (Fin 2 → Fin 3 → F) → ↥Q := Function.surjInv hβQs
  let sΦ : Multiplicative (Fin 1 → Fin 3 → F) → ↥Φ := Function.surjInv hβΦs
  have hsQ : ∀ m, βQ (sQ m) = m := Function.surjInv_eq hβQs
  have hsΦ : ∀ m, βΦ (sΦ m) = m := Function.surjInv_eq hβΦs
  let φk : Fin 3 → ↥Φ := fun k => sΦ (Multiplicative.ofAdd (fun _ => Pi.single k 1))
  have hφk : ∀ k, Multiplicative.toAdd (βΦ (φk k)) 0 = Pi.single k 1 := by
    intro k
    show Multiplicative.toAdd (βΦ (sΦ _)) 0 = _
    rw [hsΦ]; rfl
  let m : (Fin 2 → Fin 3 → F) → (Fin 3 → ↥W) := fun x k => c (sQ (Multiplicative.ofAdd x)) (φk k)
  have hinj : Function.Injective m := by
    intro x x' h
    set q : ↥Q := sQ (Multiplicative.ofAdd x) with hq
    set q' : ↥Q := sQ (Multiplicative.ofAdd x') with hq'
    have hk : ∀ k, ((q⁻¹ * q' : ↥Q) : G) * (φk k : G) = (φk k : G) * ((q⁻¹ * q' : ↥Q) : G) := by
      intro k
      have hk1 : (q : G) * (φk k) * (q : G)⁻¹ * (φk k : G)⁻¹ =
          (q' : G) * (φk k) * (q' : G)⁻¹ * (φk k : G)⁻¹ :=
        congrArg (fun w : ↥W => (w : G)) (congrFun h k)
      have hmul := comm_mul_left' hZQ hZc (q := (q : G)) (q' := ((q⁻¹ * q' : ↥Q) : G))
        (φ := (φk k : G)) q.2 (hcomZ q q.2 _ (φk k).2) (hcomZ _ (q⁻¹ * q').2 _ (φk k).2)
      have hqq : (q : G) * ((q⁻¹ * q' : ↥Q) : G) = (q' : G) := by simp
      rw [hqq, ← hk1] at hmul
      have hY : ((q⁻¹ * q' : ↥Q) : G) * (φk k : G) * ((q⁻¹ * q' : ↥Q) : G)⁻¹ * (φk k : G)⁻¹ = 1 :=
        mul_left_cancel (a := (q : G) * (φk k) * (q : G)⁻¹ * (φk k : G)⁻¹)
          (by rw [mul_one]; exact hmul.symm)
      have := hY
      calc ((q⁻¹ * q' : ↥Q) : G) * (φk k : G)
          = (((q⁻¹ * q' : ↥Q) : G) * (φk k : G) * ((q⁻¹ * q' : ↥Q) : G)⁻¹ * (φk k : G)⁻¹) *
              ((φk k : G) * ((q⁻¹ * q' : ↥Q) : G)) := by group
        _ = _ := by rw [hY, one_mul]
    have hKmem : ((q⁻¹ * q' : ↥Q) : G) ∈ K :=
      hKdef' _ (q⁻¹ * q').2 (hcomm_all (q⁻¹ * q') φk hφk hk)
    have hker : (q⁻¹ * q' : ↥Q) ∈ βQ.ker := by
      rw [hβQk, Subgroup.mem_subgroupOf]; exact hKmem
    rw [MonoidHom.mem_ker, map_mul, map_inv, inv_mul_eq_one] at hker
    have := hker.symm
    rw [hq, hq', hsQ, hsQ] at this
    exact Multiplicative.ofAdd.injective this.symm
  have hcard : Nat.card (Fin 2 → Fin 3 → F) ≤ Nat.card (Fin 3 → ↥W) :=
    Nat.card_le_card_of_injective m hinj
  have h64 : Nat.card (Fin 2 → Fin 3 → F) = 64 := by
    simp [Nat.card_fun, Nat.card_eq_fintype_card, hF]
  have hW3 : Nat.card (Fin 3 → ↥W) = Nat.card ↥W ^ 3 := by
    simp [Nat.card_fun]
  rw [h64, hW3] at hcard
  have h4 : 4 ≤ Nat.card ↥W := by
    by_contra hlt
    have : Nat.card ↥W ≤ 3 := by omega
    have : Nat.card ↥W ^ 3 ≤ 3 ^ 3 := Nat.pow_le_pow_left this 3
    omega
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [hC4]; exact h4)

end Main

end Stellmacher.PU.L3YC

end CFSG.Quasithin
