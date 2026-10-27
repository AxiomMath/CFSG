module

public import CFSG.Quasithin.MS93.S36Two
public import CFSG.Quasithin.Vol2.KGNatSemiLin

public section

namespace CFSG.Quasithin.MS93.S36

open CFSG.Quasithin CFSG.Assembly.LowTwoRank CFSG.Quasithin.Vol2 Matrix

variable {G : Type} [Group G] {F : Type} [Field F] {L U : Subgroup G}
  {a : ↥L →* ↥(StatedSL 3 F)} (N : NatSec L U ⊥ a false)

@[expose] def IsCoordMap (t : G) (f : (Fin 3 → F) →+ (Fin 3 → F)) : Prop :=
  ∀ u ∈ U, N.coord (t * u * t⁻¹) = f (N.coord u)

@[expose] def IsFClosed (K : Subgroup G) : Prop :=
  ∀ x ∈ K, ∀ y ∈ U, ∀ c : F, N.coord y = c • N.coord x → y ∈ K

section CoordMap

theorem conj_mem_of_normalizer {t : G} (ht : t ∈ Subgroup.normalizer (U : Set G)) {u : G}
    (hu : u ∈ U) : t * u * t⁻¹ ∈ U :=
  (Subgroup.mem_normalizer_iff.mp ht u).mp hu

theorem coord_ne_zero {u : G} (hu : u ∈ U) (hu1 : u ≠ 1) : N.coord u ≠ 0 := fun h =>
  hu1 (N.eq_one_of_coord_eq_zero hu h)

theorem exists_isCoordMap {t : G} (ht : t ∈ Subgroup.normalizer (U : Set G)) :
    ∃ f, IsCoordMap N t f := by
  choose s hs hsc using N.exists_coord_eq
  have hs1 : s 0 = 1 := N.eq_of_coord_eq (hs 0) U.one_mem (by rw [hsc, N.coord_one])
  have hsmul : ∀ x y, s (x + y) = s x * s y := fun x y =>
    N.eq_of_coord_eq (hs _) (U.mul_mem (hs x) (hs y))
      (by rw [hsc, N.coord_mul (hs x) (hs y), hsc, hsc])
  refine ⟨{ toFun := fun y => N.coord (t * s y * t⁻¹), map_zero' := ?_, map_add' := ?_ }, ?_⟩
  · show N.coord (t * s 0 * t⁻¹) = 0
    rw [hs1, mul_one, mul_inv_cancel, N.coord_one]
  · intro x y
    show N.coord (t * s (x + y) * t⁻¹) = N.coord (t * s x * t⁻¹) + N.coord (t * s y * t⁻¹)
    rw [hsmul, show t * (s x * s y) * t⁻¹ = (t * s x * t⁻¹) * (t * s y * t⁻¹) by group,
      N.coord_mul (conj_mem_of_normalizer ht (hs x)) (conj_mem_of_normalizer ht (hs y))]
  · intro u hu
    simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk]
    rw [N.eq_of_coord_eq (hs _) hu (hsc _)]

variable {N}

theorem isCoordMap_one : IsCoordMap N 1 (AddMonoidHom.id _) := by
  intro u _
  rw [one_mul, inv_one, mul_one]
  rfl

theorem IsCoordMap.mul {t t' : G} {f f' : (Fin 3 → F) →+ (Fin 3 → F)} (hf : IsCoordMap N t f)
    (hf' : IsCoordMap N t' f') (ht' : t' ∈ Subgroup.normalizer (U : Set G)) :
    IsCoordMap N (t * t') (f.comp f') := by
  intro u hu
  rw [show t * t' * u * (t * t')⁻¹ = t * (t' * u * t'⁻¹) * t⁻¹ by group,
    hf _ (conj_mem_of_normalizer ht' hu), hf' u hu]
  rfl

theorem IsCoordMap.unique {t : G} {f f' : (Fin 3 → F) →+ (Fin 3 → F)} (hf : IsCoordMap N t f)
    (hf' : IsCoordMap N t f') : f = f' := by
  refine AddMonoidHom.ext fun y => ?_
  obtain ⟨u, hu, rfl⟩ := N.exists_coord_eq y
  rw [← hf u hu, ← hf' u hu]

theorem IsCoordMap.inv_apply {t : G} {f f' : (Fin 3 → F) →+ (Fin 3 → F)} (hf : IsCoordMap N t f)
    (hf' : IsCoordMap N t⁻¹ f') (ht : t ∈ Subgroup.normalizer (U : Set G)) (x : Fin 3 → F) :
    f (f' x) = x ∧ f' (f x) = x := by
  have h1 := hf.mul hf' (inv_mem ht)
  have h2 := hf'.mul hf ht
  rw [mul_inv_cancel] at h1
  rw [inv_mul_cancel] at h2
  exact ⟨congrArg (fun g : (Fin 3 → F) →+ (Fin 3 → F) => g x) (h1.unique isCoordMap_one),
    congrArg (fun g : (Fin 3 → F) →+ (Fin 3 → F) => g x) (h2.unique isCoordMap_one)⟩

theorem IsCoordMap.pow {t : G} {f : (Fin 3 → F) →+ (Fin 3 → F)} (hf : IsCoordMap N t f)
    (ht : t ∈ Subgroup.normalizer (U : Set G)) (k : ℕ) {u : G} (hu : u ∈ U) :
    N.coord (t ^ k * u * (t ^ k)⁻¹) = (⇑f)^[k] (N.coord u) := by
  induction k generalizing u with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply, ← hf u hu, ← ih (conj_mem_of_normalizer ht hu)]
    congr 1
    group

theorem coord_conj_L (l : ↥L) {u : G} (hu : u ∈ U) :
    N.coord ((l : G) * u * (l : G)⁻¹) = ((a l : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ
      N.coord u := by
  rw [N.coord_conj l hu, natAct_false, coe_toSL3]

theorem IsCoordMap.conj_mulVec {t : G} {f : (Fin 3 → F) →+ (Fin 3 → F)} (hf : IsCoordMap N t f)
    (htU : t ∈ Subgroup.normalizer (U : Set G)) (htL : t ∈ Subgroup.normalizer (L : Set G))
    (l : ↥L) (y : Fin 3 → F) :
    f (((a l : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ y) =
      ((a ⟨t * l * t⁻¹, (Subgroup.mem_normalizer_iff.mp htL l).mp l.2⟩ : GL (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F) *ᵥ f y := by
  obtain ⟨u, hu, rfl⟩ := N.exists_coord_eq y
  rw [← coord_conj_L l hu, ← hf _ (N.conj_mem l hu), ← hf u hu,
    ← coord_conj_L _ (conj_mem_of_normalizer htU hu)]
  congr 1
  simp only
  group

theorem IsCoordMap.semilinear (ha : Function.Surjective a) {t : G}
    (htU : t ∈ Subgroup.normalizer (U : Set G)) (htL : t ∈ Subgroup.normalizer (L : Set G))
    {f : (Fin 3 → F) →+ (Fin 3 → F)} (hf : IsCoordMap N t f) :
    ∃ σ : F →+* F, ∀ (c : F) (x : Fin 3 → F), f (c • x) = σ c • f x := by
  obtain ⟨f', hf'⟩ := exists_isCoordMap N (inv_mem htU)
  have hinv := hf.inv_apply hf' htU
  have htL' : t⁻¹ ∈ Subgroup.normalizer (L : Set G) := inv_mem htL
  have hS : ∀ c : F, ∃ s : F, ∀ x : Fin 3 → F, f (c • f' x) = s • x := by
    intro c
    let S : (Fin 3 → F) →+ (Fin 3 → F) :=
      { toFun := fun x => f (c • f' x)
        map_zero' := by simp
        map_add' := fun x y => by simp [smul_add] }
    refine KGNat.commutant_statedSL (by norm_num) S fun γ x => ?_
    rw [KGNat.linModelNat_lin, KGNat.linModelNat_lin]
    obtain ⟨l', rfl⟩ := ha γ
    have hl : t⁻¹ * (l' : G) * t⁻¹⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp htL' l').mp l'.2
    set l : ↥L := ⟨t⁻¹ * l' * t⁻¹⁻¹, hl⟩ with hldef
    have hl' : (⟨t * (l : G) * t⁻¹, (Subgroup.mem_normalizer_iff.mp htL l).mp l.2⟩ : ↥L) = l' :=
      Subtype.ext (by simp [hldef, mul_assoc])
    change f (c • f' (((a l' : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ x)) =
      ((a l' : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ f (c • f' x)
    rw [hf'.conj_mulVec (inv_mem htU) htL' l' x, ← hldef, ← Matrix.mulVec_smul,
      hf.conj_mulVec htU htL l, hl']
  choose s hs using hS
  have hfs : ∀ c x, f (c • x) = s c • f x := fun c x => by
    have := hs c (f x)
    rwa [(hinv x).2] at this
  obtain ⟨x₀, hx₀⟩ : ∃ x₀ : Fin 3 → F, f x₀ ≠ 0 := by
    refine ⟨f' (Pi.single 0 1), ?_⟩
    rw [(hinv _).1]
    exact fun h => by simpa using congrFun h 0
  have hcancel : ∀ c d : F, c • f x₀ = d • f x₀ → c = d := fun c d h =>
    smul_left_injective F hx₀ h
  refine ⟨{ toFun := s, map_one' := ?_, map_mul' := ?_, map_zero' := ?_, map_add' := ?_ },
    hfs⟩
  · exact hcancel _ _ (by rw [← hfs, one_smul, one_smul])
  · intro c d
    exact hcancel _ _ (by rw [← hfs, mul_smul, hfs, hfs, smul_smul])
  · exact hcancel _ _ (by rw [← hfs, zero_smul, zero_smul, map_zero])
  · intro c d
    exact hcancel _ _ (by rw [← hfs, add_smul, map_add, hfs, hfs, add_smul])

theorem IsCoordMap.mem_centralizer_iff {t : G} {f : (Fin 3 → F) →+ (Fin 3 → F)}
    (hf : IsCoordMap N t f) (htU : t ∈ Subgroup.normalizer (U : Set G)) {u : G} (hu : u ∈ U) :
    u ∈ Subgroup.centralizer ({t} : Set G) ↔ f (N.coord u) = N.coord u := by
  rw [Subgroup.mem_centralizer_singleton_iff, ← hf u hu]
  constructor
  · intro h
    rw [show t * u * t⁻¹ = u by rw [← h]; group]
  · intro h
    have := N.eq_of_coord_eq (conj_mem_of_normalizer htU hu) hu h
    calc u * t = t * u * t⁻¹ * t := by rw [this]
      _ = t * u := by group

theorem IsCoordMap.card_fix {t : G} {f : (Fin 3 → F) →+ (Fin 3 → F)} (hf : IsCoordMap N t f)
    (htU : t ∈ Subgroup.normalizer (U : Set G)) :
    Nat.card ↥(U ⊓ Subgroup.centralizer ({t} : Set G)) = Nat.card ↥(KGNat.fixAdd f) := by
  refine Nat.card_eq_of_bijective (fun u => ⟨N.coord u, KGNat.mem_fixAdd.mpr
    ((hf.mem_centralizer_iff htU (Subgroup.mem_inf.mp u.2).1).mp
      (Subgroup.mem_inf.mp u.2).2)⟩) ⟨fun u v huv => ?_, fun y => ?_⟩
  · exact Subtype.ext (N.eq_of_coord_eq (Subgroup.mem_inf.mp u.2).1 (Subgroup.mem_inf.mp v.2).1
      (congrArg Subtype.val huv))
  · obtain ⟨u, hu, hcu⟩ := N.exists_coord_eq y
    have hfix : f (N.coord u) = N.coord u := by rw [hcu]; exact KGNat.mem_fixAdd.mp y.2
    exact ⟨⟨u, Subgroup.mem_inf.mpr ⟨hu, (hf.mem_centralizer_iff htU hu).mpr hfix⟩⟩,
      Subtype.ext hcu⟩

theorem card_eq_card_fin3 [Finite F] (N : NatSec L U ⊥ a false) :
    Nat.card ↥U = Nat.card (Fin 3 → F) := by
  rw [N.card_eq, Nat.card_fun, Nat.card_eq_fintype_card (α := Fin 3), Fintype.card_fin]

theorem IsCoordMap.linear_of_card [Finite F] (ha : Function.Surjective a) {t : G}
    (htU : t ∈ Subgroup.normalizer (U : Set G)) (htL : t ∈ Subgroup.normalizer (L : Set G))
    {f : (Fin 3 → F) →+ (Fin 3 → F)} (hf : IsCoordMap N t f)
    (hcard : Nat.card ↥U < Nat.card ↥(U ⊓ Subgroup.centralizer ({t} : Set G)) ^ 2) :
    ∀ (c : F) (x : Fin 3 → F), f (c • x) = c • f x := by
  obtain ⟨σ, hσ⟩ := hf.semilinear ha htU htL
  rw [hf.card_fix htU, card_eq_card_fin3 N] at hcard
  have hid := KGNat.semilinear_eq_id_of_card_fix hσ hcard
  intro c x
  rw [hσ, hid]

end CoordMap

section FClosed

variable {N}

theorem isFClosed_commImg (hU : ∀ x ∈ U, ∀ y ∈ U, x * y = y * x) {t : G}
    (htU : t ∈ Subgroup.normalizer (U : Set G)) {f : (Fin 3 → F) →+ (Fin 3 → F)}
    (hf : IsCoordMap N t f) (hlin : ∀ (c : F) (x : Fin 3 → F), f (c • x) = c • f x) :
    IsFClosed N (commImg hU htU) := by
  intro x hx y hy c hc
  obtain ⟨u, hu, rfl⟩ := (mem_commImg hU htU).mp hx
  obtain ⟨w, hw, hcw⟩ := N.exists_coord_eq (c • N.coord u)
  have hwc : t * w * t⁻¹ * w⁻¹ ∈ U := U.mul_mem (conj_mem_of_normalizer htU hw) (U.inv_mem hw)
  have hcoord : ∀ v ∈ U, N.coord (t * v * t⁻¹ * v⁻¹) = f (N.coord v) - N.coord v := by
    intro v hv
    rw [N.coord_mul (conj_mem_of_normalizer htU hv) (U.inv_mem hv), N.coord_inv hv, hf v hv,
      sub_eq_add_neg]
  have : y = t * w * t⁻¹ * w⁻¹ := by
    refine N.eq_of_coord_eq hy hwc ?_
    rw [hc, hcoord u hu, hcoord w hw, hcw, hlin, smul_sub]
  rw [this]
  exact (mem_commImg hU htU).mpr ⟨w, hw, rfl⟩

theorem isFClosed_fix {t : G} (htU : t ∈ Subgroup.normalizer (U : Set G))
    {f : (Fin 3 → F) →+ (Fin 3 → F)} (hf : IsCoordMap N t f)
    (hlin : ∀ (c : F) (x : Fin 3 → F), f (c • x) = c • f x) :
    IsFClosed N (U ⊓ Subgroup.centralizer ({t} : Set G)) := by
  intro x hx y hy c hc
  refine ⟨hy, (hf.mem_centralizer_iff htU hy).mpr ?_⟩
  rw [hc, hlin, (hf.mem_centralizer_iff htU (Subgroup.mem_inf.mp hx).1).mp
    (Subgroup.mem_inf.mp hx).2]

theorem IsFClosed.conj {K : Subgroup G} (hK : IsFClosed N K) (hKU : K ≤ U) (l : ↥L) :
    IsFClosed N (K.map (MulAut.conj (l : G)).toMonoidHom) := by
  rintro _ ⟨k, hk, rfl⟩ y hy c hc
  obtain ⟨w, hw, hcw⟩ := N.exists_coord_eq (c • N.coord k)
  have hwK : w ∈ K := hK k hk w hw c hcw
  refine ⟨w, hwK, ?_⟩
  refine N.eq_of_coord_eq (N.conj_mem l hw) hy ?_
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hc
  show N.coord ((l : G) * w * (l : G)⁻¹) = N.coord y
  rw [hc, coord_conj_L l (hKU hk), coord_conj_L l hw, hcw, Matrix.mulVec_smul]

variable (N) in
theorem exists_line {x : G} (hx : x ∈ U) (hx1 : x ≠ 1) :
    ∃ P : Subgroup G, P ≤ U ∧ Nat.card ↥P = Nat.card F ∧
      ∀ y ∈ U, (y ∈ P ↔ ∃ c : F, N.coord y = c • N.coord x) := by
  set S : AddSubgroup (Fin 3 → F) := (Submodule.span F {N.coord x}).toAddSubgroup with hS
  refine ⟨N.pre S, fun y hy => ((N.mem_pre).mp hy).1, ?_, fun y hy => ?_⟩
  · have hx0 := coord_ne_zero N hx hx1
    symm
    refine Nat.card_eq_of_bijective (fun c => (⟨_, (N.mem_pre).mpr
      ⟨(Classical.choose_spec (N.exists_coord_eq (c • N.coord x))).1, ?_⟩⟩ : ↥(N.pre S)))
      ⟨fun c d hcd => ?_, fun y => ?_⟩
    · rw [(Classical.choose_spec (N.exists_coord_eq (c • N.coord x))).2]
      exact Submodule.mem_span_singleton.mpr ⟨c, rfl⟩
    · have h := congrArg (fun v : ↥(N.pre S) => N.coord (v : G)) hcd
      simp only [(Classical.choose_spec (N.exists_coord_eq _)).2] at h
      exact smul_left_injective F hx0 h
    · obtain ⟨hyU, hyS⟩ := (N.mem_pre).mp y.2
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hyS
      refine ⟨c, Subtype.ext (N.eq_of_coord_eq
        (Classical.choose_spec (N.exists_coord_eq (c • N.coord x))).1 hyU ?_)⟩
      rw [(Classical.choose_spec (N.exists_coord_eq _)).2, hc]
  · rw [N.mem_pre, hS]
    simp only [Submodule.mem_toAddSubgroup, Submodule.mem_span_singleton]
    exact ⟨fun h => let ⟨c, hc⟩ := h.2; ⟨c, hc.symm⟩, fun ⟨c, hc⟩ => ⟨hy, c, hc.symm⟩⟩

variable [Finite G]

theorem IsFClosed.eq_line {P : Subgroup G} (hP : IsFClosed N P)
    (hcP : Nat.card ↥P = Nat.card F) {x : G} (hx : x ∈ P) {Q' : Subgroup G}
    (hQ'U : Q' ≤ U) (hcQ' : Nat.card ↥Q' = Nat.card F)
    (hQ' : ∀ y ∈ U, (y ∈ Q' ↔ ∃ c : F, N.coord y = c • N.coord x)) : P = Q' := by
  refine (Subgroup.eq_of_le_of_card_ge (fun y hy => ?_) (by rw [hcP, hcQ'])).symm
  obtain ⟨c, hc⟩ := (hQ' y (hQ'U hy)).mp hy
  exact hP x hx y (hQ'U hy) c hc

theorem eq_of_isFClosed {P P' : Subgroup G} (hP : IsFClosed N P) (hP' : IsFClosed N P')
    (hPU : P ≤ U) (hcP : Nat.card ↥P = Nat.card F)
    (hcP' : Nat.card ↥P' = Nat.card F) {x : G} (hx : x ∈ P) (hx' : x ∈ P') (hx1 : x ≠ 1) :
    P = P' := by
  obtain ⟨S, hSU, hcS, hS⟩ := exists_line N (hPU hx) hx1
  rw [hP.eq_line hcP hx hSU hcS hS, hP'.eq_line hcP' hx' hSU hcS hS]

theorem IsFClosed.card_ge {P : Subgroup G} (hP : IsFClosed N P) (hPU : P ≤ U) (hP1 : P ≠ ⊥) :
    Nat.card F ≤ Nat.card ↥P := by
  obtain ⟨⟨x, hx⟩, hx1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hP1
  obtain ⟨S, hSU, hcS, hS⟩ := exists_line N (hPU hx) (fun h => hx1 (Subtype.ext h))
  rw [← hcS]
  refine Subgroup.card_le_of_le fun y hy => ?_
  obtain ⟨c, hc⟩ := (hS y (hSU hy)).mp hy
  exact hP x hx y (hSU hy) c hc

end FClosed

section Linear

variable {N}

theorem IsCoordMap.linear_of_le (ha : Function.Surjective a) {t : G}
    (htU : t ∈ Subgroup.normalizer (U : Set G)) (htL : t ∈ Subgroup.normalizer (L : Set G))
    {f : (Fin 3 → F) →+ (Fin 3 → F)} (hf : IsCoordMap N t f) {E : Subgroup G}
    (hE : IsFClosed N E) (hEU : E ≤ U) (hUE : ¬ U ≤ E)
    (hcomm : ∀ u ∈ U, t * u * t⁻¹ * u⁻¹ ∈ E) : ∀ (c : F) (x : Fin 3 → F), f (c • x) = c • f x := by
  obtain ⟨σ, hσ⟩ := hf.semilinear ha htU htL
  by_cases hσ1 : ∀ c, σ c = c
  · intro c x
    rw [hσ, hσ1]
  exfalso
  push Not at hσ1
  obtain ⟨c, hc⟩ := hσ1
  apply hUE
  have hcoord : ∀ v ∈ U, N.coord (t * v * t⁻¹ * v⁻¹) = f (N.coord v) - N.coord v := by
    intro v hv
    rw [N.coord_mul (conj_mem_of_normalizer htU hv) (U.inv_mem hv), N.coord_inv hv, hf v hv,
      sub_eq_add_neg]
  have key : ∀ w ∈ U, t * w * t⁻¹ ∈ E := by
    intro w hw
    obtain ⟨w', hw', hcw'⟩ := N.exists_coord_eq (c • N.coord w)
    have he₁ := hcomm w hw
    have he₂ := hcomm w' hw'
    obtain ⟨e₃, he₃U, hce₃⟩ := N.exists_coord_eq (c • N.coord (t * w * t⁻¹ * w⁻¹))
    have he₃ : e₃ ∈ E := hE _ he₁ e₃ he₃U c hce₃
    have he₄ : (t * w' * t⁻¹ * w'⁻¹) * e₃⁻¹ ∈ E := E.mul_mem he₂ (E.inv_mem he₃)
    have hc4 : N.coord ((t * w' * t⁻¹ * w'⁻¹) * e₃⁻¹) = (σ c - c) • N.coord (t * w * t⁻¹) := by
      rw [N.coord_mul (hEU he₂) (U.inv_mem he₃U), N.coord_inv he₃U, hce₃, hcoord w' hw',
        hcoord w hw, hcw', hσ, hf w hw]
      module
    have hne : σ c - c ≠ 0 := sub_ne_zero.mpr hc
    refine hE _ he₄ _ (conj_mem_of_normalizer htU hw) (σ c - c)⁻¹ ?_
    rw [hc4, smul_smul, inv_mul_cancel₀ hne, one_smul]
  intro u hu
  have hu' : t⁻¹ * u * t⁻¹⁻¹ ∈ U := conj_mem_of_normalizer (inv_mem htU) hu
  have := key _ hu'
  rwa [show t * (t⁻¹ * u * t⁻¹⁻¹) * t⁻¹ = u by group] at this

variable [CharP F 2]

theorem eq_one_of_pow_two_pow {μ : F} {e : ℕ} (h : μ ^ 2 ^ e = 1) : μ = 1 := by
  have h1 : (μ - 1) ^ 2 ^ e = 0 := by rw [sub_pow_char_pow, h, one_pow, sub_self]
  exact sub_eq_zero.mp (pow_eq_zero_iff (pow_ne_zero _ two_ne_zero) |>.mp h1)

variable [Finite F] [Finite G]

theorem commutator_mem_of_two {E₁ E₂ : Subgroup G} (hE₁ : IsFClosed N E₁) (hE₂ : IsFClosed N E₂)
    (h12 : E₁ ≤ E₂) (h2U : E₂ ≤ U) (hc₁ : Nat.card ↥E₁ = Nat.card F)
    (hc₂ : Nat.card ↥E₂ = Nat.card F * Nat.card F) {t : G}
    (htU : t ∈ Subgroup.normalizer (U : Set G)) {f : (Fin 3 → F) →+ (Fin 3 → F)}
    (hf : IsCoordMap N t f) (hlin : ∀ (c : F) (x : Fin 3 → F), f (c • x) = c • f x)
    (hn₁ : ∀ x ∈ E₁, t * x * t⁻¹ ∈ E₁) (hn₂ : ∀ x ∈ E₂, t * x * t⁻¹ ∈ E₂) {e : ℕ}
    (ht2 : t ^ 2 ^ e = 1) {x : G} (hx : x ∈ E₂) :
    t * x * t⁻¹ * x⁻¹ ∈ E₁ := by
  have hU1 : E₁ ≤ U := h12.trans h2U
  have hmem₁ : ∀ v ∈ U, ∀ e₁ ∈ E₁, N.coord v = N.coord e₁ → v ∈ E₁ := fun v hv e₁ he₁ h =>
    (N.eq_of_coord_eq hv (hU1 he₁) h).symm ▸ he₁
  have hsmul₁ : ∀ e₁ ∈ E₁, ∀ c : F, ∃ e' ∈ E₁, N.coord e' = c • N.coord e₁ := fun e₁ he₁ c => by
    obtain ⟨w, hw, hcw⟩ := N.exists_coord_eq (c • N.coord e₁)
    exact ⟨w, hE₁ e₁ he₁ w hw c hcw, hcw⟩
  obtain ⟨p, hp₂, hp₁⟩ : ∃ p ∈ E₂, p ∉ E₁ := by
    by_contra hall
    push Not at hall
    have hle : E₂ ≤ E₁ := fun y hy => hall y hy
    have := Subgroup.card_le_of_le hle
    rw [hc₁, hc₂] at this
    have hq : 1 < Nat.card F := Finite.one_lt_card
    nlinarith
  have hpU := h2U hp₂
  have hdec : ∀ y ∈ E₂, ∃ c : F, ∃ r ∈ E₁, N.coord y = c • N.coord p + N.coord r := by
    let φ : F × ↥E₁ → ↥E₂ := fun cr =>
      ⟨Classical.choose (N.exists_coord_eq (cr.1 • N.coord p + N.coord (cr.2 : G))),
        by
          obtain ⟨hvU, hv⟩ := Classical.choose_spec
            (N.exists_coord_eq (cr.1 • N.coord p + N.coord (cr.2 : G)))
          obtain ⟨w, hw, hcw⟩ := N.exists_coord_eq (cr.1 • N.coord p)
          have hwE : w ∈ E₂ := hE₂ p hp₂ w hw cr.1 hcw
          have : Classical.choose (N.exists_coord_eq (cr.1 • N.coord p + N.coord (cr.2 : G))) =
              w * cr.2 := N.eq_of_coord_eq hvU (U.mul_mem hw (hU1 cr.2.2))
            (by rw [hv, N.coord_mul hw (hU1 cr.2.2), hcw])
          rw [this]
          exact E₂.mul_mem hwE (h12 cr.2.2)⟩
    have hφc : ∀ cr, N.coord (φ cr : G) = cr.1 • N.coord p + N.coord (cr.2 : G) := fun cr =>
      (Classical.choose_spec (N.exists_coord_eq (cr.1 • N.coord p + N.coord (cr.2 : G)))).2
    have hinj : Function.Injective φ := by
      rintro ⟨c, r⟩ ⟨d, s⟩ h
      have h1 := congrArg (fun v : ↥E₂ => N.coord (v : G)) h
      simp only [hφc] at h1
      have hcd : c = d := by
        by_contra hne
        apply hp₁
        obtain ⟨e', he', hce'⟩ := hsmul₁ _ (E₁.mul_mem s.2 (E₁.inv_mem r.2)) (c - d)⁻¹
        refine hmem₁ p hpU e' he' ?_
        rw [hce', N.coord_mul (hU1 s.2) (U.inv_mem (hU1 r.2)), N.coord_inv (hU1 r.2)]
        have h2 : (c - d) • N.coord p = N.coord (s : G) - N.coord (r : G) := by
          rw [sub_smul]
          linear_combination (norm := module) h1
        rw [← sub_eq_add_neg, ← h2, smul_smul, inv_mul_cancel₀ (sub_ne_zero.mpr hne), one_smul]
      subst hcd
      have h2 : N.coord (r : G) = N.coord (s : G) := by simpa using h1
      exact Prod.ext rfl (Subtype.ext (N.eq_of_coord_eq (hU1 r.2) (hU1 s.2) h2))
    have hsurj : Function.Surjective φ := by
      refine (hinj.bijective_of_nat_card_le ?_).2
      rw [Nat.card_prod, hc₁, hc₂]
    intro y hy
    obtain ⟨⟨c, r⟩, hcr⟩ := hsurj ⟨y, hy⟩
    refine ⟨c, r, r.2, ?_⟩
    have h1 := hφc (c, r)
    rw [hcr] at h1
    exact h1
  obtain ⟨μ, r₀, hr₀, hμ⟩ := hdec _ (hn₂ p hp₂)
  rw [hf p hpU] at hμ
  have hiter : ∀ k : ℕ, ∃ r ∈ E₁, (⇑f)^[k] (N.coord p) = μ ^ k • N.coord p + N.coord r := by
    intro k
    induction k with
    | zero => exact ⟨1, E₁.one_mem, by simp [N.coord_one]⟩
    | succ k ih =>
      obtain ⟨r, hr, hrk⟩ := ih
      obtain ⟨r', hr', hcr'⟩ := hsmul₁ r₀ hr₀ (μ ^ k)
      refine ⟨r' * (t * r * t⁻¹), E₁.mul_mem hr' (hn₁ r hr), ?_⟩
      rw [Function.iterate_succ_apply', hrk, map_add, hlin, hμ, ← hf r (hU1 hr),
        N.coord_mul (hU1 hr') (hU1 (hn₁ r hr)), hcr', smul_add, smul_smul, pow_succ]
      abel
  have hid : (⇑f)^[2 ^ e] (N.coord p) = N.coord p := by
    rw [← hf.pow htU (2 ^ e) hpU, ht2, one_mul, inv_one, mul_one]
  obtain ⟨r, hr, hrk⟩ := hiter (2 ^ e)
  rw [hid] at hrk
  have hμ1 : μ = 1 := by
    refine eq_one_of_pow_two_pow (e := e) ?_
    by_contra hne
    apply hp₁
    have h1 : (1 - μ ^ 2 ^ e) • N.coord p = N.coord r := by
      rw [sub_smul, one_smul]
      linear_combination (norm := module) hrk
    obtain ⟨e', he', hce'⟩ := hsmul₁ r hr (1 - μ ^ 2 ^ e)⁻¹
    refine hmem₁ p hpU e' he' ?_
    rw [hce', ← h1, smul_smul, inv_mul_cancel₀ (sub_ne_zero.mpr (Ne.symm hne)), one_smul]
  obtain ⟨c, r₁, hr₁, hcx⟩ := hdec x hx
  have hxU := h2U hx
  have hcoord : N.coord (t * x * t⁻¹ * x⁻¹) = c • N.coord r₀ +
      (N.coord (t * r₁ * t⁻¹) - N.coord r₁) := by
    rw [N.coord_mul (conj_mem_of_normalizer htU hxU) (U.inv_mem hxU), N.coord_inv hxU,
      hf x hxU, hcx, map_add, hlin, hμ, hμ1, one_smul, hf r₁ (hU1 hr₁)]
    module
  obtain ⟨e₁, he₁, hce₁⟩ := hsmul₁ r₀ hr₀ c
  have hmem : e₁ * ((t * r₁ * t⁻¹) * r₁⁻¹) ∈ E₁ :=
    E₁.mul_mem he₁ (E₁.mul_mem (hn₁ r₁ hr₁) (E₁.inv_mem hr₁))
  refine hmem₁ _ (U.mul_mem (conj_mem_of_normalizer htU hxU) (U.inv_mem hxU)) _ hmem ?_
  rw [hcoord, N.coord_mul (hU1 he₁) (U.mul_mem (hU1 (hn₁ r₁ hr₁)) (U.inv_mem (hU1 hr₁))),
    N.coord_mul (hU1 (hn₁ r₁ hr₁)) (U.inv_mem (hU1 hr₁)), N.coord_inv (hU1 hr₁), hce₁,
    sub_eq_add_neg]

omit [Finite F] [Finite G] in
theorem IsCoordMap.exists_eq_conj (ha : Function.Surjective a) {t : G}
    (htU : t ∈ Subgroup.normalizer (U : Set G)) {f : (Fin 3 → F) →+ (Fin 3 → F)}
    (hf : IsCoordMap N t f) (hlin : ∀ (c : F) (x : Fin 3 → F), f (c • x) = c • f x) {e : ℕ}
    (ht2 : t ^ 2 ^ e = 1) : ∃ l : ↥L, ∀ u ∈ U, t * u * t⁻¹ = (l : G) * u * (l : G)⁻¹ := by
  let fl : (Fin 3 → F) →ₗ[F] (Fin 3 → F) :=
    { toFun := f, map_add' := map_add f, map_smul' := hlin }
  set A := LinearMap.toMatrix' fl with hA
  have hAx : ∀ x, A *ᵥ x = f x := fun x => by
    rw [hA, LinearMap.toMatrix'_mulVec]
    rfl
  have hpowx : ∀ (k : ℕ) (y : Fin 3 → F), (A ^ k) *ᵥ y = (⇑f)^[k] y := by
    intro k
    induction k with
    | zero => intro y; simp
    | succ k ih =>
      intro y
      rw [pow_succ', ← Matrix.mulVec_mulVec, ih, hAx, Function.iterate_succ_apply']
  have hiter : ∀ x, (A ^ 2 ^ e) *ᵥ x = x := by
    intro x
    obtain ⟨u, hu, rfl⟩ := N.exists_coord_eq x
    have h1 := hf.pow htU (2 ^ e) hu
    rw [ht2, one_mul, inv_one, mul_one] at h1
    rw [hpowx, ← h1]
  have hApow : A ^ 2 ^ e = 1 := by
    ext i j
    have := congrFun (hiter (Pi.single j 1)) i
    rw [Matrix.mulVec_single_one, Matrix.col_apply] at this
    rw [this, Matrix.one_apply, Pi.single_apply]
  have hdet : A.det = 1 := by
    have := congrArg Matrix.det hApow
    rw [Matrix.det_pow, Matrix.det_one] at this
    exact eq_one_of_pow_two_pow this
  let sl : SL3 F := ⟨A, hdet⟩
  obtain ⟨l, hl⟩ := ha (specialLinearGroupEquivStatedSL 3 F sl)
  refine ⟨l, fun u hu => N.eq_of_coord_eq (conj_mem_of_normalizer htU hu) (N.conj_mem l hu) ?_⟩
  rw [hf u hu, coord_conj_L l hu, hl, specialLinearGroupEquivStatedSL_coe]
  exact (hAx _).symm

end Linear

end CFSG.Quasithin.MS93.S36
