module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKSumTwoCent
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKExcRank
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKSumTwoData
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKEndSL
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKSLAut
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKStarNat
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKQuotMap

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G] {D : Data G} {V₀ V L : Subgroup G}
  {hV : IsElemAbelian 2 V}

private noncomputable def s16kRestrictAct {W : Type} [CommGroup W] (H : Subgroup (MulAut W))
    (I : Subgroup W) (hI : ∀ h ∈ H, ∀ x ∈ I, h x ∈ I) : ↥H →* MulAut ↥I where
  toFun h :=
    { toFun := fun x => ⟨(h : MulAut W) (x : W), hI (h : MulAut W) h.2 (x : W) x.2⟩
      invFun := fun x => ⟨(h : MulAut W)⁻¹ (x : W),
        hI (h : MulAut W)⁻¹ (inv_mem h.2) (x : W) x.2⟩
      left_inv := fun x => Subtype.ext (by simp)
      right_inv := fun x => Subtype.ext (by simp)
      map_mul' := fun x y => Subtype.ext (map_mul (h : MulAut W) (x : W) (y : W)) }
  map_one' := by ext x; rfl
  map_mul' := fun a b => by ext x; rfl

private theorem s16kRealizesRestrict {W : Type} [CommGroup W] {H : Subgroup (MulAut W)}
    {I : Subgroup W} (hI : ∀ h ∈ H, ∀ x ∈ I, h x ∈ I) {D : FFModel}
    (hR : D.Realizes H I ⊥) :
    D.Realizes (s16kRestrictAct H I hI).range ⊤ ⊥ := by
  obtain ⟨π, hsurj, -, hks, -, -, hsec, hker, β, hβs, hβk, hβe⟩ := hR
  let res := s16kRestrictAct H I hI
  let π' : D.Gam →* ↥res.range :=
    (res.comp π).codRestrict res.range fun γ => ⟨π γ, rfl⟩
  have hπ's : Function.Surjective π' := by
    rintro ⟨y, h, rfl⟩
    obtain ⟨γ, rfl⟩ := hsurj h
    exact ⟨γ, Subtype.ext rfl⟩
  let β' : ↥(⊤ : Subgroup ↥I) →* ↥D.sec ⧸ D.ker.subgroupOf D.sec :=
    β.comp (Subgroup.topEquiv (G := ↥I)).toMonoidHom
  refine ⟨π', hπ's, bot_le, hks, (fun _ _ _ => Subgroup.mem_top _), (fun _ z hz => ?_), hsec, hker,
    β', hβs.comp (Subgroup.topEquiv).surjective, ?_, ?_⟩
  · rw [Subgroup.mem_bot] at hz ⊢
    rw [hz, map_one]
  · intro u
    rw [MonoidHom.comp_apply, hβk]
    constructor
    · intro h
      exact Subgroup.mem_bot.2 (Subtype.ext (Subgroup.mem_bot.1 h))
    · intro h
      exact Subgroup.mem_bot.2 (congrArg Subtype.val (Subgroup.mem_bot.1 h))
  · intro γ u m _ hm hβu
    have hu' : ((π γ : ↥H) : MulAut W)
        (((Subgroup.topEquiv (G := ↥I)) u : ↥I) : W) ∈ I :=
      hI (π γ) (π γ).2 _ ((Subgroup.topEquiv (G := ↥I)) u).2
    have h1 : β' ⟨(π' γ : MulAut ↥I) u, Subgroup.mem_top _⟩ =
        β ⟨((π γ : ↥H) : MulAut W)
          (((Subgroup.topEquiv (G := ↥I)) u : ↥I) : W), hu'⟩ := rfl
    rw [h1]
    exact hβe γ ((Subgroup.topEquiv (G := ↥I)) u) m hu' hm hβu

private theorem s16kMapCentralizer {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    (S : Subgroup X) :
    (Subgroup.centralizer (S : Set X)).map e.toMonoidHom =
      Subgroup.centralizer ((S.map e.toMonoidHom : Subgroup Y) : Set Y) := by
  apply le_antisymm
  · exact Subgroup.map_centralizer_le_centralizer_image (S : Set X) e.toMonoidHom
  · intro y hy
    rw [Subgroup.mem_map]
    refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
    rw [Subgroup.mem_centralizer_iff] at hy ⊢
    intro s hs
    have h2 := hy (e s) (Subgroup.mem_map_of_mem _ hs)
    apply e.injective
    rw [map_mul, map_mul]
    simpa using h2

private noncomputable def s16kProdHom {Q : Type} [CommGroup Q] (A B : Subgroup Q) :
    ↥A × ↥B →* Q where
  toFun x := (x.1 : Q) * (x.2 : Q)
  map_one' := by simp
  map_mul' := fun x y => by
    show ((x.1 : Q) * (y.1 : Q)) * ((x.2 : Q) * (y.2 : Q)) =
      ((x.1 : Q) * (x.2 : Q)) * ((y.1 : Q) * (y.2 : Q))
    ac_rfl

private theorem s16kProdHom_injective {Q : Type} [CommGroup Q] {A B : Subgroup Q}
    (hinf : A ⊓ B = ⊥) : Function.Injective (s16kProdHom A B) := by
  intro x y hxy
  have hxy' : (x.1 : Q) * (x.2 : Q) = (y.1 : Q) * (y.2 : Q) := hxy
  have h1 : (y.1 : Q)⁻¹ * (x.1 : Q) = (y.2 : Q) * (x.2 : Q)⁻¹ := by
    calc (y.1 : Q)⁻¹ * (x.1 : Q)
        = (y.1 : Q)⁻¹ * ((x.1 : Q) * (x.2 : Q)) * (x.2 : Q)⁻¹ := by group
      _ = (y.1 : Q)⁻¹ * ((y.1 : Q) * (y.2 : Q)) * (x.2 : Q)⁻¹ := by rw [hxy']
      _ = (y.2 : Q) * (x.2 : Q)⁻¹ := by group
  have hmemA : (y.1 : Q)⁻¹ * (x.1 : Q) ∈ A := A.mul_mem (A.inv_mem y.1.2) x.1.2
  have hmemB : (y.2 : Q) * (x.2 : Q)⁻¹ ∈ B := B.mul_mem y.2.2 (B.inv_mem x.2.2)
  have hbot : (y.1 : Q)⁻¹ * (x.1 : Q) ∈ (⊥ : Subgroup Q) := by
    rw [← hinf]
    exact ⟨hmemA, h1 ▸ hmemB⟩
  rw [Subgroup.mem_bot] at hbot
  have hx1 : (x.1 : Q) = (y.1 : Q) := by
    have h := congrArg (fun z => (y.1 : Q) * z) hbot
    simpa using h
  have hx2 : (y.2 : Q) = (x.2 : Q) := by
    have hb2 : (y.2 : Q) * (x.2 : Q)⁻¹ = 1 := h1 ▸ hbot
    have h := congrArg (fun z => z * (x.2 : Q)) hb2
    simpa using h
  exact Prod.ext (Subtype.ext hx1) (Subtype.ext hx2.symm)

private theorem s16kProdHom_surjective {Q : Type} [CommGroup Q] {A B : Subgroup Q}
    (hsup : A ⊔ B = ⊤) : Function.Surjective (s16kProdHom A B) := by
  intro q
  have hq : q ∈ A ⊔ B := by rw [hsup]; exact Subgroup.mem_top q
  obtain ⟨a, ha, b, hb, hab⟩ := Subgroup.mem_sup.1 hq
  exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), hab⟩

private noncomputable def s16kProdEquiv {Q : Type} [CommGroup Q] {A B : Subgroup Q}
    (hinf : A ⊓ B = ⊥) (hsup : A ⊔ B = ⊤) : ↥A × ↥B ≃* Q :=
  MulEquiv.ofBijective (s16kProdHom A B)
    ⟨s16kProdHom_injective hinf, s16kProdHom_surjective hsup⟩

theorem s16k_pRank_mbar_le_two (h : S16gRowCtx D V₀ V L hV) {n : ℕ} (hn : n = 6 ∨ n = 7)
    (hSL : IsSLn ↥(lBar V₀ V hV L) n 1)
    (hS : SumOfNat (fun H U Z => BinaryNaturalSL H U Z n 1) (lBar V₀ V hV L)
      (commSub ⊤ (lBar V₀ V hV L)) (commSub ⊤ (lBar V₀ V hV L) ⊓ fixV (lBar V₀ V hV L)) 2)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    (hAut : CFSG.Open.pRank p (⊤ : Subgroup (MulAut ↥(lBar V₀ V hV L))) ≤ 2) :
    CFSG.Open.pRank p (Mbar D.M V₀ V hV) ≤ 2 := by
  have hn2 : 2 ≤ n := by rcases hn with rfl | rfl <;> norm_num
  obtain ⟨Q, hQc, hQf, q, ρ, hqsurj, hqker, hρinj, hρeq, hQsq, -, -⟩ :=
    s16k_exists_quot_map h
  letI := hQc
  letI := hQf
  let H := lBar V₀ V hV L
  let Z := fixV H
  let A := Mbar D.M V₀ V hV
  let L' := ρ.range
  have hqker' : q.ker = Z := by ext x; rw [MonoidHom.mem_ker, hqker]
  have hHA : H ≤ A := barSub_mono V₀ V hV h.setting.hyp151.le
  have hHn : ∀ a ∈ A, ∀ b ∈ H, a * b * a⁻¹ ∈ H :=
    fun a ha b hb => (Subgroup.mem_normalizer_iff.1 (h.mBar_le_normalizer ha) b).1 hb
  have hZA : ∀ a ∈ A, ∀ z ∈ Z, a z ∈ Z := by
    intro a ha z hz
    rw [mem_fixV] at hz ⊢
    intro h hh
    have hmem : a⁻¹ * h * a ∈ H := by
      have h2 := hHn a⁻¹ (inv_mem ha) h hh
      simpa using h2
    calc h (a z) = a ((a⁻¹ * h * a) z) := by simp [MulAut.mul_apply]
      _ = a z := by rw [hz _ hmem]
  have hφ : ∀ a : ↥A, ∃ f : MulAut Q, ∀ x : Vtil V₀ V hV, f (q x) = q ((a : MulAut _) x) := by
    intro a
    refine s16g_exists_induced_aut q hqsurj (φ := (a : MulAut _)) (fun x => ?_)
    rw [hqker x, hqker ((a : MulAut _) x)]
    exact ⟨fun hx => hZA a a.2 x hx, fun hx => by
      simpa using hZA a⁻¹ (inv_mem a.2) ((a : MulAut _) x) hx⟩
  choose φ hφspec using hφ
  have hφ1 : φ 1 = 1 := by
    ext y
    obtain ⟨x, rfl⟩ := hqsurj y
    rw [hφspec 1 x]
    simp
  have hφm : ∀ a b : ↥A, φ (a * b) = φ a * φ b := by
    intro a b
    ext y
    obtain ⟨x, rfl⟩ := hqsurj y
    rw [hφspec (a * b) x, MulAut.mul_apply, hφspec b x, hφspec a ((b : MulAut _) x)]
    rfl
  let φhom : ↥A →* MulAut Q := { toFun := φ, map_one' := hφ1, map_mul' := hφm }
  have hφspec' : ∀ (a : ↥A) (x : Vtil V₀ V hV), φhom a (q x) = q ((a : MulAut _) x) :=
    fun a x => hφspec a x
  have hφρ : ∀ h : ↥H, φhom ⟨(h : MulAut _), hHA h.2⟩ = ρ h := by
    intro h
    ext y
    obtain ⟨x, rfl⟩ := hqsurj y
    rw [hφspec' ⟨(h : MulAut _), hHA h.2⟩ x, hρeq h x]
  have hφinj : Function.Injective φhom := by
    rw [injective_iff_map_eq_one]
    intro a ha
    have hafix : ∀ x : Vtil V₀ V hV, (a : MulAut _) x * x⁻¹ ∈ Z := by
      intro x
      have h1 : q ((a : MulAut _) x * x⁻¹) = 1 := by
        rw [map_mul, map_inv, ← hφspec' a x, ha]
        simp
      exact (hqker _).1 h1
    have hac : ∀ h ∈ H, (a : MulAut _) * h = h * (a : MulAut _) := by
      intro h hh
      have hmem : (a : MulAut _) * h * (a : MulAut _)⁻¹ * h⁻¹ ∈ H :=
        H.mul_mem (hHn a a.2 h hh) (H.inv_mem hh)
      have hker : ρ ⟨(a : MulAut _) * h * (a : MulAut _)⁻¹ * h⁻¹, hmem⟩ = 1 := by
        have h1 : φhom ⟨(a : MulAut _) * h * (a : MulAut _)⁻¹ * h⁻¹, hHA hmem⟩ = 1 := by
          have heq : (⟨(a : MulAut _) * h * (a : MulAut _)⁻¹ * h⁻¹, hHA hmem⟩ : ↥A) =
              a * ⟨h, hHA hh⟩ * a⁻¹ * ⟨h, hHA hh⟩⁻¹ := Subtype.ext rfl
          show φhom _ = 1
          rw [heq, map_mul, map_mul, map_mul, map_inv, map_inv, ha, hφρ ⟨h, hh⟩]
          simp
        have h2 := hφρ (⟨(a : MulAut _) * h * (a : MulAut _)⁻¹ * h⁻¹, hmem⟩ : ↥H)
        exact h2.symm.trans h1
      have h1 : (⟨(a : MulAut _) * h * (a : MulAut _)⁻¹ * h⁻¹, hmem⟩ : ↥H) = 1 :=
        hρinj (by rw [hker, map_one])
      have h2 : (a : MulAut _) * h * (a : MulAut _)⁻¹ * h⁻¹ = 1 := by
        simpa using congrArg Subtype.val h1
      have h4 : (a : MulAut _) * h * (a : MulAut _)⁻¹ = h := mul_inv_eq_one.1 h2
      calc (a : MulAut _) * h
          = (a : MulAut _) * h * (a : MulAut _)⁻¹ * (a : MulAut _) := by group
        _ = h * (a : MulAut _) := by rw [h4]
    have ha1 : (a : MulAut _) = 1 := s16g_eq_one_of_commSub h.comm_top hac hafix
    exact Subtype.ext ha1
  let N := φhom.range
  have hNnorm : ∀ n ∈ N, ∀ l ∈ L', n * l * n⁻¹ ∈ L' := by
    intro n hn l hl
    obtain ⟨a, rfl⟩ := hn
    obtain ⟨h, rfl⟩ := hl
    have hmem : (a : MulAut _) * (h : MulAut _) * (a : MulAut _)⁻¹ ∈ H := hHn a a.2 h h.2
    refine ⟨⟨(a : MulAut _) * (h : MulAut _) * (a : MulAut _)⁻¹, hmem⟩, ?_⟩
    have heq : (⟨(a : MulAut _) * (h : MulAut _) * (a : MulAut _)⁻¹, hHA hmem⟩ : ↥A) =
        a * ⟨(h : MulAut _), hHA h.2⟩ * a⁻¹ := Subtype.ext rfl
    rw [← hφρ ⟨_, hmem⟩, heq, map_mul, map_mul, map_inv, hφρ ⟨h, h.2⟩]
  have hrank : CFSG.Open.pRank p A ≤ CFSG.Open.pRank p N := by
    rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup A]
    have h := CFSG.SectionRank.pRank_le_map hp.one_lt φhom hφinj (⊤ : Subgroup ↥A)
    rw [← MonoidHom.range_eq_map] at h
    exact h
  have hC : CFSG.Open.pRank p (Subgroup.centralizer (L' : Set (MulAut Q))) = 0 := by
    obtain ⟨I₁, I₂, hZ₁, hZ₂, hind₁, hind₂, hsupI, hN₁, hN₂⟩ := s16k_sum_two_data h hS
    obtain ⟨K₁, hF₁, hFin₁, hK₁, hR₁⟩ := hN₁
    obtain ⟨K₂, hF₂, hFin₂, hK₂, hR₂⟩ := hN₂
    have hinv₁ : ∀ (h : ↥H), ∀ u ∈ I₁, (h : MulAut _) u ∈ I₁ := by
      obtain ⟨π₁, hπ₁⟩ := hR₁
      exact hπ₁.2.2.2.1
    have hinv₂ : ∀ (h : ↥H), ∀ u ∈ I₂, (h : MulAut _) u ∈ I₂ := by
      obtain ⟨π₂, hπ₂⟩ := hR₂
      exact hπ₂.2.2.2.1
    let Q₁ := I₁.map q
    let Q₂ := I₂.map q
    have hinf : Q₁ ⊓ Q₂ = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      intro z hz
      rw [Subgroup.mem_inf] at hz
      obtain ⟨hz₁, hz₂⟩ := hz
      obtain ⟨x, hx₁, hxq⟩ := Subgroup.mem_map.1 hz₁
      obtain ⟨y, hy₂, hyq⟩ := Subgroup.mem_map.1 hz₂
      have hxy : x * y⁻¹ ∈ Z := by
        rw [← hqker']
        rw [MonoidHom.mem_ker, map_mul, map_inv, hxq, hyq, mul_inv_cancel]
      have hxZ : x ∈ Z ⊔ I₂ := by
        have h1 : x = (x * y⁻¹) * y := by group
        rw [h1]
        exact (Z ⊔ I₂).mul_mem ((le_sup_left : Z ≤ Z ⊔ I₂) hxy)
          ((le_sup_right : I₂ ≤ Z ⊔ I₂) hy₂)
      have hxZ' : x ∈ Z := hind₁ ⟨hx₁, hxZ⟩
      rw [← hxq]
      exact (hqker x).2 hxZ'
    have hsup' : Q₁ ⊔ Q₂ = ⊤ := by
      have hZmap : Z.map q = ⊥ := by rw [Subgroup.map_eq_bot_iff, hqker']
      have h1 : (⊤ : Subgroup (Vtil V₀ V hV)).map q = ⊤ :=
        Subgroup.map_top_of_surjective q hqsurj
      rw [← hsupI] at h1
      rw [Subgroup.map_sup, Subgroup.map_sup, hZmap, bot_sup_eq] at h1
      exact h1
    have hQ₁inv : ∀ h ∈ ρ.range, ∀ x ∈ Q₁, h x ∈ Q₁ := by
      intro h hh x hx
      obtain ⟨l, rfl⟩ := hh
      obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.1 hx
      rw [← hρeq l w]
      exact Subgroup.mem_map_of_mem _ (hinv₁ l w hw)
    have hQ₂inv : ∀ h ∈ ρ.range, ∀ x ∈ Q₂, h x ∈ Q₂ := by
      intro h hh x hx
      obtain ⟨l, rfl⟩ := hh
      obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.1 hx
      rw [← hρeq l w]
      exact Subgroup.mem_map_of_mem _ (hinv₂ l w hw)
    let ρ₁ := s16kRestrictAct ρ.range Q₁ hQ₁inv
    let ρ₂ := s16kRestrictAct ρ.range Q₂ hQ₂inv
    have hReal₁ : (FFModel.nat (StatedSL n K₁)).Realizes ρ₁.range ⊤ ⊥ :=
      s16kRealizesRestrict hQ₁inv
        (s16k_realizes_map_bot hR₁ q hqker' ρ.rangeRestrict
          (MonoidHom.rangeRestrict_surjective ρ)
          (fun (l : ↥H) (x : Vtil V₀ V hV) => hρeq l x))
    have hReal₂ : (FFModel.nat (StatedSL n K₂)).Realizes ρ₂.range ⊤ ⊥ :=
      s16kRealizesRestrict hQ₂inv
        (s16k_realizes_map_bot hR₂ q hqker' ρ.rangeRestrict
          (MonoidHom.rangeRestrict_surjective ρ)
          (fun (l : ↥H) (x : Vtil V₀ V hV) => hρeq l x))
    have hirr₁ : ∀ B : Subgroup ↥Q₁,
        (∀ l : ↥ρ.range, ∀ b ∈ B, ρ₁ l b ∈ B) → B = ⊥ ∨ B = ⊤ := by
      intro B hB
      obtain ⟨π, hπ⟩ := hReal₁
      have hI := CFSG.Quasithin.B5.isIrr_of_realizes (K := K₁) hn2 hπ
      exact hI.2.2 B (fun a b hb => by
        obtain ⟨l, hl⟩ := MonoidHom.mem_range.1 a.2
        rw [show a • b = ρ₁ l b by rw [hl]; rfl]
        exact hB l b hb) bot_le le_top
    have hirr₂ : ∀ B : Subgroup ↥Q₂,
        (∀ l : ↥ρ.range, ∀ b ∈ B, ρ₂ l b ∈ B) → B = ⊥ ∨ B = ⊤ := by
      intro B hB
      obtain ⟨π, hπ⟩ := hReal₂
      have hI := CFSG.Quasithin.B5.isIrr_of_realizes (K := K₂) hn2 hπ
      exact hI.2.2 B (fun a b hb => by
        obtain ⟨l, hl⟩ := MonoidHom.mem_range.1 a.2
        rw [show a • b = ρ₂ l b by rw [hl]; rfl]
        exact hB l b hb) bot_le le_top
    have hC₁ : Subgroup.centralizer
        ((ρ₁.range : Subgroup (MulAut ↥Q₁)) : Set (MulAut ↥Q₁)) = ⊥ := by
      refine s16k_centralizer_sl_natural (K := K₁) hn2 ?_ hReal₁
      rw [hK₁, pow_one]
    have hC₂ : Subgroup.centralizer
        ((ρ₂.range : Subgroup (MulAut ↥Q₂)) : Set (MulAut ↥Q₂)) = ⊥ := by
      refine s16k_centralizer_sl_natural (K := K₂) hn2 ?_ hReal₂
      rw [hK₂, pow_one]
    let ρdiag : ↥ρ.range →* MulAut (↥Q₁ × ↥Q₂) :=
      { toFun := fun l => MulEquiv.prodCongr (ρ₁ l) (ρ₂ l)
        map_one' := by
          apply MulEquiv.ext
          intro x
          show (ρ₁ 1 x.1, ρ₂ 1 x.2) = x
          rw [map_one, map_one]
          rfl
        map_mul' := fun a b => by
          apply MulEquiv.ext
          intro x
          show (ρ₁ (a * b) x.1, ρ₂ (a * b) x.2) =
            (ρ₁ a (ρ₁ b x.1), ρ₂ a (ρ₂ b x.2))
          rw [map_mul, map_mul]
          rfl }
    have hρdiag : ∀ (l : ↥ρ.range) (x : ↥Q₁ × ↥Q₂),
        ρdiag l x = (ρ₁ l x.1, ρ₂ l x.2) := fun l x => rfl
    have hcent := s16k_pRank_centralizer_prod ρ₁ ρ₂
      (fun x : ↥Q₁ => Subtype.ext (hQsq (x : Q)))
      (fun x : ↥Q₂ => Subtype.ext (hQsq (x : Q)))
      hirr₁ hirr₂ hC₁ hC₂ ρdiag hρdiag hp hp2
    rw [if_neg hp3] at hcent
    let e := s16kProdEquiv hinf hsup'
    have hcongr : ∀ l : ↥ρ.range, (MulAut.congr e) (ρdiag l) = (l : MulAut Q) := by
      intro l
      ext x
      rw [MulAut.congr_apply]
      show e (ρdiag l (e.symm x)) = (l : MulAut Q) x
      have h1 : e (ρdiag l (e.symm x)) = (l : MulAut Q) (e (e.symm x)) := by
        show ((ρ₁ l (e.symm x).1 : ↥Q₁) : Q) * ((ρ₂ l (e.symm x).2 : ↥Q₂) : Q) =
          (l : MulAut Q) (((e.symm x).1 : Q) * ((e.symm x).2 : Q))
        rw [map_mul]
        rfl
      rw [h1, MulEquiv.apply_symm_apply]
    have hmap : (ρdiag.range : Subgroup (MulAut (↥Q₁ × ↥Q₂))).map
        (MulAut.congr e).toMonoidHom = L' := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        obtain ⟨l, rfl⟩ := hx
        change (MulAut.congr e) (ρdiag l) ∈ L'
        rw [hcongr l]
        exact l.2
      · intro hy
        obtain ⟨l, rfl⟩ := hy
        refine ⟨ρdiag ⟨ρ l, ⟨l, rfl⟩⟩, ⟨⟨ρ l, ⟨l, rfl⟩⟩, rfl⟩, ?_⟩
        change (MulAut.congr e) (ρdiag ⟨ρ l, ⟨l, rfl⟩⟩) = ρ l
        rw [hcongr ⟨ρ l, ⟨l, rfl⟩⟩]
    have hmap' : (L' : Subgroup (MulAut Q)).map (MulAut.congr e).symm.toMonoidHom =
        ρdiag.range := by
      rw [← hmap, Subgroup.map_map,
        show (MulAut.congr e).symm.toMonoidHom.comp (MulAut.congr e).toMonoidHom =
          MonoidHom.id (MulAut (↥Q₁ × ↥Q₂)) from by
            apply MonoidHom.ext
            intro x
            exact MulEquiv.symm_apply_apply (MulAut.congr e) x, Subgroup.map_id]
    have hbound : CFSG.Open.pRank p (Subgroup.centralizer (L' : Set (MulAut Q))) ≤
        CFSG.Open.pRank p (Subgroup.centralizer
          ((ρdiag.range : Subgroup (MulAut (↥Q₁ × ↥Q₂))) :
            Set (MulAut (↥Q₁ × ↥Q₂)))) := by
      have h := CFSG.SectionRank.pRank_le_map hp.one_lt (MulAut.congr e).symm.toMonoidHom
        (MulAut.congr e).symm.injective (Subgroup.centralizer (L' : Set (MulAut Q)))
      rwa [s16kMapCentralizer (MulAut.congr e).symm L', hmap'] at h
    exact le_antisymm (hbound.trans hcent) (Nat.zero_le _)
  have hbound := s16k_pRank_le_of_normalizer (Q := Q) (L' := L') (N := N) hNnorm hp
  have hAutL' : CFSG.Open.pRank p (⊤ : Subgroup (MulAut ↥L')) ≤ 2 := by
    rw [← s16k_pRank_mulAut_congr (MonoidHom.ofInjective hρinj) p]
    exact hAut
  calc CFSG.Open.pRank p A ≤ CFSG.Open.pRank p N := hrank
    _ ≤ CFSG.Open.pRank p (N ⊓ Subgroup.centralizer (L' : Set (MulAut Q))) +
        CFSG.Open.pRank p (⊤ : Subgroup (MulAut ↥L')) := hbound
    _ ≤ 0 + 2 := add_le_add
        (le_trans (CFSG.SectionRank.pRank_mono hp.one_lt inf_le_right) (le_of_eq hC)) hAutL'
    _ = 2 := by norm_num

theorem s16k_three_mem_sig_sl_small (h : S16gRowCtx D V₀ V L hV) {n : ℕ} (hn : n = 6 ∨ n = 7)
    (hSL : IsSLn ↥(lBar V₀ V hV L) n 1)
    (hS : SumOfNat (fun H U Z => BinaryNaturalSL H U Z n 1) (lBar V₀ V hV L)
      (commSub ⊤ (lBar V₀ V hV L)) (commSub ⊤ (lBar V₀ V hV L) ⊓ fixV (lBar V₀ V hV L)) 2) :
    3 ∈ D.sig := by
  by_contra h3
  obtain ⟨p, hpσ⟩ := h.std.hx.sig_nonempty
  have hp : p.Prime := (D.sig_prime p hpσ).1
  have hp2 : p ≠ 2 := (D.sig_prime p hpσ).2
  have hp3 : p ≠ 3 := fun hp3 => h3 (hp3 ▸ hpσ)
  have hrk := h.three_le_pRank hpσ
  have hAut := s16k_pRank_aut_sl_small hn hSL hp hp2 hp3
  have hle := s16k_pRank_mbar_le_two h hn hSL hS hp hp2 hp3 hAut
  omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
