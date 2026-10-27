module

public import CFSG.Quasithin.Background.RonanF13Singer

public section

namespace CFSG.Quasithin.RonanF13

variable {K : Type*} [Group K]

@[expose] def restrictAut (H : Subgroup K) (α : MulAut K) (h : ∀ x, α x ∈ H ↔ x ∈ H) : MulAut ↥H where
  toFun x := ⟨α x, (h x).mpr x.2⟩
  invFun x := ⟨α⁻¹ x, by
    have : α (α⁻¹ (x : K)) ∈ H := by simpa using x.2
    exact (h _).mp this⟩
  left_inv x := by ext; simp
  right_inv x := by ext; simp
  map_mul' x y := by ext; simp

theorem restrictAut_apply (H : Subgroup K) (α : MulAut K) (h : ∀ x, α x ∈ H ↔ x ∈ H) (x : ↥H) :
    ((restrictAut H α h x : ↥H) : K) = α x := rfl

@[expose] def conjAut (H : Subgroup K) (d : K) (hd : d ∈ Subgroup.normalizer (H : Set K)) :
    MulAut ↥H :=
  restrictAut H (MulAut.conj d) (fun x => (Subgroup.mem_normalizer_iff.mp hd x).symm)

theorem conjAut_apply (H : Subgroup K) (d : K) (hd : d ∈ Subgroup.normalizer (H : Set K)) (x : ↥H) :
    ((conjAut H d hd x : ↥H) : K) = d * x * d⁻¹ := rfl

theorem conjAut_symm_apply (H : Subgroup K) (d : K) (hd : d ∈ Subgroup.normalizer (H : Set K))
    (x : ↥H) : (((conjAut H d hd).symm x : ↥H) : K) = d⁻¹ * x * d := by
  show (((MulAut.conj d)⁻¹ : MulAut K) (x : K)) = _
  simp

theorem singer_sections [Finite K] (A B D : Subgroup K) (hBA : B ≤ A) (hBne : B ≠ A)
    (hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y * x⁻¹ * y⁻¹ ∈ B) (hsq : ∀ x ∈ A, x * x ∈ B)
    (hDA : D ≤ Subgroup.normalizer (A : Set K)) (hDB : D ≤ Subgroup.normalizer (B : Set K))
    (hDcomm : ∀ x ∈ D, ∀ y ∈ D, x * y = y * x)
    (hirr : ∀ W : Subgroup K, B ≤ W → W ≤ A →
      (∀ d ∈ D, ∀ w ∈ W, d * w * d⁻¹ ∈ W) → W = B ∨ W = A)
    (hfaith : ∀ d ∈ D, (∀ x ∈ A, d * x * d⁻¹ * x⁻¹ ∈ B) → d = 1)
    (α : MulAut K) (hαA : ∀ x, α x ∈ A ↔ x ∈ A) (hαB : ∀ x, α x ∈ B ↔ x ∈ B)
    (hαD : ∀ x, α x ∈ D ↔ x ∈ D) :
    IsCyclic ↥D ∧ ∃ k : ℕ, ∀ d ∈ D, α d = d ^ 2 ^ k := by
  classical
  haveI hN : (B.subgroupOf A).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have h1 := hcomm g g.2 n n.2
    have h2 : (g : K) * n * (g : K)⁻¹ = ((g : K) * n * (g : K)⁻¹ * (n : K)⁻¹) * n := by group
    show (g : K) * n * (g : K)⁻¹ ∈ B
    rw [h2]
    exact B.mul_mem h1 hn⟩
  letI : CommGroup ↥D :=
    { (inferInstance : Group ↥D) with mul_comm := fun x y => Subtype.ext (hDcomm x x.2 y y.2) }
  letI : CommGroup (↥A ⧸ B.subgroupOf A) :=
    { (inferInstance : Group (↥A ⧸ B.subgroupOf A)) with
      mul_comm := fun x y => by
        induction x using QuotientGroup.induction_on with
        | H x =>
          induction y using QuotientGroup.induction_on with
          | H y =>
            rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq,
              Subgroup.mem_subgroupOf]
            have h1 := hcomm (y⁻¹ : ↥A) (y⁻¹).2 (x⁻¹ : ↥A) (x⁻¹).2
            have h2 : (((x * y)⁻¹ * (y * x) : ↥A) : K) =
                (y : K)⁻¹ * (x : K)⁻¹ * ((y : K)⁻¹)⁻¹ * ((x : K)⁻¹)⁻¹ := by
              simp [mul_assoc]
            rw [h2]
            exact h1 }
  haveI : Nontrivial (↥A ⧸ B.subgroupOf A) := by
    obtain ⟨a, haA, haB⟩ := SetLike.exists_of_lt (lt_of_le_of_ne hBA hBne)
    refine ⟨⟨QuotientGroup.mk ⟨a, haA⟩, 1, fun h => haB ?_⟩⟩
    have := (QuotientGroup.eq_one_iff (N := B.subgroupOf A) (⟨a, haA⟩ : ↥A)).mp h
    exact this
  have hV2 : ∀ v : ↥A ⧸ B.subgroupOf A, v * v = 1 := by
    intro v
    induction v using QuotientGroup.induction_on with
    | H a =>
      rw [← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      exact hsq a a.2
  have hmapc : ∀ d : ↥D,
      (B.subgroupOf A).map (conjAut A d (hDA d.2)).toMonoidHom = B.subgroupOf A := by
    intro d
    ext y
    rw [Subgroup.mem_map_equiv, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf,
      conjAut_symm_apply]
    have h1 := Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (hDB d.2)) (y : K)
    simpa using h1.symm
  let ρ : ↥D →* MulAut (↥A ⧸ B.subgroupOf A) :=
    { toFun := fun d => QuotientGroup.congr (B.subgroupOf A) (B.subgroupOf A)
        (conjAut A d (hDA d.2)) (hmapc d)
      map_one' := by
        ext x
        induction x using QuotientGroup.induction_on with
        | H x =>
          show (QuotientGroup.mk (conjAut A ((1 : ↥D) : K) (hDA (1 : ↥D).2) x) : ↥A ⧸ B.subgroupOf A) = _
          congr 1
          apply Subtype.ext
          simp [conjAut_apply]
      map_mul' := fun d d' => by
        ext x
        induction x using QuotientGroup.induction_on with
        | H x =>
          show (QuotientGroup.mk (conjAut A ((d * d' : ↥D) : K) (hDA (d * d').2) x) :
            ↥A ⧸ B.subgroupOf A) = QuotientGroup.mk (conjAut A d (hDA d.2)
              (conjAut A d' (hDA d'.2) x))
          congr 1
          apply Subtype.ext
          simp [conjAut_apply, mul_assoc] }
  have hρmk : ∀ (d : ↥D) (a : ↥A),
      ρ d (QuotientGroup.mk a : ↥A ⧸ B.subgroupOf A) =
        QuotientGroup.mk (conjAut A d (hDA d.2) a) := fun d a => rfl
  have hρ : Function.Injective ρ := by
    rw [injective_iff_map_eq_one]
    intro d hd
    apply Subtype.ext
    show (d : K) = 1
    refine hfaith d d.2 (fun x hx => ?_)
    have h1 := hρmk d ⟨x⁻¹, A.inv_mem hx⟩
    rw [hd, MulAut.one_apply] at h1
    have h2 := QuotientGroup.eq.mp h1
    rw [Subgroup.mem_subgroupOf] at h2
    have h3 : ((((⟨x⁻¹, A.inv_mem hx⟩ : ↥A))⁻¹ *
        (conjAut A d (hDA d.2) ⟨x⁻¹, A.inv_mem hx⟩) : ↥A) : K) =
          x * ((d : K) * x⁻¹ * (d : K)⁻¹) := by
      simp [conjAut_apply, mul_assoc]
    rw [h3] at h2
    have h5 : (d : K) * x * (d : K)⁻¹ * x⁻¹ = (x * ((d : K) * x⁻¹ * (d : K)⁻¹))⁻¹ := by group
    rw [h5]
    exact B.inv_mem h2
  have hirr' : ∀ W' : Subgroup (↥A ⧸ B.subgroupOf A),
      (∀ d : ↥D, ∀ w ∈ W', ρ d w ∈ W') → W' = ⊥ ∨ W' = ⊤ := by
    intro W' hW'
    let W : Subgroup K := (W'.comap (QuotientGroup.mk' (B.subgroupOf A))).map A.subtype
    have hmemW : ∀ x : K, x ∈ W ↔ ∃ a : ↥A, (a : K) = x ∧
        (QuotientGroup.mk a : ↥A ⧸ B.subgroupOf A) ∈ W' := by
      intro x
      constructor
      · intro hx
        obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hx
        exact ⟨a, rfl, ha⟩
      · rintro ⟨a, rfl, ha⟩
        exact Subgroup.mem_map.mpr ⟨a, ha, rfl⟩
    have hBW : B ≤ W := by
      intro b hb
      rw [hmemW]
      refine ⟨⟨b, hBA hb⟩, rfl, ?_⟩
      have : (QuotientGroup.mk (⟨b, hBA hb⟩ : ↥A) : ↥A ⧸ B.subgroupOf A) = 1 :=
        (QuotientGroup.eq_one_iff _).mpr (by rw [Subgroup.mem_subgroupOf]; exact hb)
      rw [this]
      exact W'.one_mem
    have hWA : W ≤ A := by
      intro x hx
      obtain ⟨a, rfl, -⟩ := (hmemW x).mp hx
      exact a.2
    have hWinv : ∀ d ∈ D, ∀ w ∈ W, d * w * d⁻¹ ∈ W := by
      intro d hd w hw
      obtain ⟨a, rfl, ha⟩ := (hmemW w).mp hw
      rw [hmemW]
      refine ⟨conjAut A d (hDA hd) a, rfl, ?_⟩
      have := hW' ⟨d, hd⟩ _ ha
      rwa [hρmk] at this
    rcases hirr W hBW hWA hWinv with h | h
    · left
      rw [eq_bot_iff]
      intro v hv
      induction v using QuotientGroup.induction_on with
      | H a =>
        have : (a : K) ∈ W := (hmemW _).mpr ⟨a, rfl, hv⟩
        rw [h] at this
        have : (QuotientGroup.mk a : ↥A ⧸ B.subgroupOf A) = 1 :=
          (QuotientGroup.eq_one_iff _).mpr (by rw [Subgroup.mem_subgroupOf]; exact this)
        rw [this]
        exact Subgroup.one_mem _
    · right
      rw [eq_top_iff]
      intro v _
      induction v using QuotientGroup.induction_on with
      | H a =>
        have : (a : K) ∈ W := by rw [h]; exact a.2
        obtain ⟨a', ha', hmk⟩ := (hmemW _).mp this
        have : a' = a := Subtype.ext ha'
        rw [this] at hmk
        exact hmk
  let ψ : MulAut ↥D := restrictAut D α hαD
  have hmapα : (B.subgroupOf A).map (restrictAut A α hαA).toMonoidHom = B.subgroupOf A := by
    ext y
    rw [Subgroup.mem_map_equiv, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    show (α⁻¹ (y : K)) ∈ B ↔ (y : K) ∈ B
    have h1 := hαB (α⁻¹ (y : K))
    simpa using h1.symm
  let Aq : MulAut (↥A ⧸ B.subgroupOf A) :=
    QuotientGroup.congr (B.subgroupOf A) (B.subgroupOf A) (restrictAut A α hαA) hmapα
  have hAmk : ∀ a : ↥A, Aq (QuotientGroup.mk a : ↥A ⧸ B.subgroupOf A) =
      QuotientGroup.mk (restrictAut A α hαA a) := fun a => rfl
  have hA : ∀ (d : ↥D) (v : ↥A ⧸ B.subgroupOf A), Aq (ρ d v) = ρ (ψ d) (Aq v) := by
    intro d v
    induction v using QuotientGroup.induction_on with
    | H a =>
      rw [hρmk, hAmk, hAmk, hρmk]
      congr 1
      apply Subtype.ext
      simp [conjAut_apply, restrictAut_apply, ψ]
  obtain ⟨hcyc, k, hk⟩ := singer_frobenius hV2 ρ hρ hirr' ψ Aq hA
  refine ⟨hcyc, k, fun d hd => ?_⟩
  have := congrArg Subtype.val (hk ⟨d, hd⟩)
  simpa [ψ, restrictAut_apply] using this

end CFSG.Quasithin.RonanF13
