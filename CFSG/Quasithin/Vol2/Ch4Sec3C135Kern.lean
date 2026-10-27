module

public import CFSG.Quasithin.Vol2.Ch4Sec3C135Cent

public section

namespace CFSG.Quasithin.H13.Ch4.C135

open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.A4
open CFSG.Open hiding StatedSL
open CFSG.Assembly.LowTwoRank CFSG.Quasithin.H13.Ch4 Matrix
open scoped commutatorElement

variable {G : Type} [Group G] {F : Type} [Field F]

structure Hyp135 (G₀ L : Subgroup G) (α : ↥L →* ↥(StatedSL 3 F)) : Prop where
  surj : IsModO2Surj L α
  le : L ≤ G₀
  norm : G₀ ≤ Subgroup.normalizer (L : Set G)
  perf : ⁅L, L⁆ = L
  nat : IsSumOfNaturalModulesVia L (centerOf (c134Q G₀ L)) ⊥ α false 1
  dual : IsSumOfNaturalModulesVia L (c134Q G₀ L) (centerOf (c134Q G₀ L)) α true 2
  cent : G₀ ⊓ Subgroup.centralizer (L : Set G) = ⊥
  scalar : ∃ c : F, c ≠ 0 ∧ c ≠ 1 ∧ c * c ≠ 1

theorem commutator_mem_Q {G₀ L : Subgroup G} {t g : G} (ht : t ∈ pCoreOf 2 G₀) (hg : g ∈ L) :
    t⁻¹ * g * t * g⁻¹ ∈ c134Q G₀ L := by
  have h := Subgroup.commutator_mem_commutator ((pCoreOf 2 G₀).inv_mem ht) hg
  rw [commutatorElement_def, inv_inv] at h
  exact h

@[expose] def cm {G₀ L : Subgroup G} {x : G} (hx : x ∈ pCoreOf 2 G₀) (y : ↥L) :
    ↥(c134Q G₀ L) :=
  ⟨x⁻¹ * y * x * (y : G)⁻¹, commutator_mem_Q hx y.2⟩

theorem coe_cm {G₀ L : Subgroup G} {x : G} (hx : x ∈ pCoreOf 2 G₀) (y : ↥L) :
    ((cm hx y : ↥(c134Q G₀ L)) : G) = x⁻¹ * y * x * (y : G)⁻¹ := rfl

theorem mul_comm_U {G₀ L : Subgroup G} {u v : G} (hu : u ∈ centerOf (c134Q G₀ L))
    (hv : v ∈ centerOf (c134Q G₀ L)) : u * v = v * u :=
  (Subgroup.mem_centralizer_iff.mp hv.2 u hu.1)

theorem eq_zero_of_fixed {k : ℕ} {x : Fin k → Fin 3 → F}
    (hx : ∀ γ : Matrix.SpecialLinearGroup (Fin 3) F,
      dact (γ : Matrix (Fin 3) (Fin 3) F) x = x) : x = 0 := by
  classical
  funext i j
  obtain ⟨l, hl⟩ : ∃ l : Fin 3, l ≠ j := by
    by_cases h0 : j = 0
    · exact ⟨1, by rw [h0]; decide⟩
    · exact ⟨0, fun h' => h0 h'.symm⟩
  have h1 := congrFun (congrFun (hx (Matrix.SpecialLinearGroup.transvection hl 1)) i) l
  simp only [dact, transvection_mulVec, Pi.add_apply, Pi.single_eq_same, one_mul] at h1
  simpa using h1

namespace Hyp135

variable {G₀ L : Subgroup G} {α : ↥L →* ↥(StatedSL 3 F)} (H : Hyp135 G₀ L α)
include H

noncomputable abbrev ρd (_ : Hyp135 G₀ L α) : ↥L →* Matrix.SpecialLinearGroup (Fin 3) F :=
  dualHom.comp (slNat α)

theorem ρd_surjective : Function.Surjective H.ρd := by
  intro γ
  obtain ⟨g, hg⟩ := slNat_surjective H.surj.1 (dualHom γ)
  exact ⟨g, by rw [MonoidHom.comp_apply, hg, dualHom_dualHom]⟩

theorem ρd_eq_one {a : ↥L} (ha : α a = 1) : H.ρd a = 1 := by
  rw [MonoidHom.comp_apply, (slNat_eq_one_iff a).mpr ha, map_one]

theorem c134Q_le_pCoreOf : c134Q G₀ L ≤ pCoreOf 2 G₀ :=
  commutator_le_left_of_le_normalizer (H.le.trans (le_normalizer_pCoreOf 2 G₀))

omit H in
theorem centerOf_le' : centerOf (c134Q G₀ L) ≤ c134Q G₀ L := inf_le_left

theorem le_normalizer_Q : G₀ ≤ Subgroup.normalizer (c134Q G₀ L : Set G) :=
  le_normalizer_c134Q H.norm

theorem le_normalizer_U : G₀ ≤ Subgroup.normalizer (centerOf (c134Q G₀ L) : Set G) :=
  le_normalizer_centerOf H.le_normalizer_Q

theorem pCoreOf_le_normalizer_Q : pCoreOf 2 G₀ ≤ Subgroup.normalizer (c134Q G₀ L : Set G) :=
  (pCoreOf_le 2 G₀).trans H.le_normalizer_Q

theorem crd_conj_ker {a : ↥L} (ha : α a = 1) (u v : ↥(c134Q G₀ L))
    (huv : (v : G) = a * u * a⁻¹) : crd H.dual v = crd H.dual u := by
  rw [crd_conj_true H.dual a u v huv, (slNat_eq_one_iff a).mpr ha, map_one]
  funext i
  simp [dact]

theorem crd_conj_Q (c u v : ↥(c134Q G₀ L)) (huv : (v : G) = c * u * (c : G)⁻¹) :
    crd H.dual v = crd H.dual u := by
  have h1 : v = c * u * c⁻¹ := Subtype.ext (by simp [huv])
  rw [h1, crd_mul, crd_mul, crd_inv]
  abel

theorem crd_cm_mul {x : G} (hx : x ∈ pCoreOf 2 G₀) (y y' : ↥L) :
    crd H.dual (cm hx (y * y')) = crd H.dual (cm hx y) +
      dact ((H.ρd y : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)
        (crd H.dual (cm hx y')) := by
  have hmem : (y : G) * (cm hx y' : G) * (y : G)⁻¹ ∈ c134Q G₀ L :=
    (Subgroup.mem_normalizer_iff.mp (H.le_normalizer_Q (H.le y.2)) _).mp (cm hx y').2
  have e : cm hx (y * y') = cm hx y * ⟨_, hmem⟩ := by
    apply Subtype.ext
    simp only [cm, Subgroup.coe_mul]
    group
  rw [e, crd_mul, crd_conj_true H.dual y (cm hx y') ⟨_, hmem⟩ rfl]
  rfl

theorem mem_centralizer_of_triv {y z : G} (hyN : y ∈ Subgroup.normalizer (c134Q G₀ L : Set G))
    (hzN : z ∈ Subgroup.normalizer (c134Q G₀ L : Set G))
    (hy : ∀ q, crd H.dual (cnj hyN q) = crd H.dual q)
    (hz : ∀ q, crd H.dual (cnj hzN q) = crd H.dual q)
    (hyU : ∀ u ∈ centerOf (c134Q G₀ L), y * u = u * y)
    (hzU : ∀ u ∈ centerOf (c134Q G₀ L), z * u = u * z) :
    y * z * y⁻¹ * z⁻¹ ∈ Subgroup.centralizer (c134Q G₀ L : Set G) := by
  have he : ∀ {w : G} (hwN : w ∈ Subgroup.normalizer (c134Q G₀ L : Set G)),
      (∀ q, crd H.dual (cnj hwN q) = crd H.dual q) → ∀ q : ↥(c134Q G₀ L),
        ∃ e ∈ centerOf (c134Q G₀ L), w * q * w⁻¹ = q * e := by
    intro w hwN hw q
    have h1 := (crd_eq_iff H.dual q (cnj hwN q)).mp (hw q).symm
    refine ⟨_, h1, ?_⟩
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_cnj]
    group
  have hcomm : ∀ q : ↥(c134Q G₀ L), (y * z) * q * (y * z)⁻¹ = (z * y) * q * (z * y)⁻¹ := by
    intro q
    obtain ⟨e₁, he₁, h₁⟩ := he hyN hy q
    obtain ⟨e₂, he₂, h₂⟩ := he hzN hz q
    have hye : y * e₂ * y⁻¹ = e₂ := by rw [hyU e₂ he₂]; group
    have hze : z * e₁ * z⁻¹ = e₁ := by rw [hzU e₁ he₁]; group
    calc (y * z) * q * (y * z)⁻¹ = y * (z * q * z⁻¹) * y⁻¹ := by group
      _ = y * (q * e₂) * y⁻¹ := by rw [h₂]
      _ = (y * q * y⁻¹) * (y * e₂ * y⁻¹) := by group
      _ = q * e₁ * e₂ := by rw [h₁, hye]
      _ = q * e₂ * e₁ := by rw [mul_assoc, mul_comm_U he₁ he₂, ← mul_assoc]
      _ = (z * q * z⁻¹) * (z * e₁ * z⁻¹) := by rw [h₂, hze]
      _ = z * (q * e₁) * z⁻¹ := by group
      _ = z * (y * q * y⁻¹) * z⁻¹ := by rw [h₁]
      _ = (z * y) * q * (z * y)⁻¹ := by group
  refine Subgroup.mem_centralizer_iff.mpr fun q hq => ?_
  have hq' : (z * y)⁻¹ * q * (z * y) ∈ c134Q G₀ L := by
    have := (Subgroup.mem_normalizer_iff.mp
      ((Subgroup.normalizer (c134Q G₀ L : Set G)).inv_mem
        ((Subgroup.normalizer (c134Q G₀ L : Set G)).mul_mem hzN hyN)) q).mp hq
    simpa using this
  have h1 := hcomm ⟨_, hq'⟩
  simp only at h1
  have h2 : (y * z * y⁻¹ * z⁻¹) * q * (y * z * y⁻¹ * z⁻¹)⁻¹ = q := by
    have e : (y * z * y⁻¹ * z⁻¹) * q * (y * z * y⁻¹ * z⁻¹)⁻¹ =
        y * z * ((z * y)⁻¹ * q * (z * y)) * (y * z)⁻¹ := by group
    rw [e, h1]
    group
  calc q * (y * z * y⁻¹ * z⁻¹) =
        ((y * z * y⁻¹ * z⁻¹) * q * (y * z * y⁻¹ * z⁻¹)⁻¹) * (y * z * y⁻¹ * z⁻¹) := by rw [h2]
    _ = (y * z * y⁻¹ * z⁻¹) * q := by group

theorem eq_one_of_equivariant (δ : ↥(c134Q G₀ L) → ↥(centerOf (c134Q G₀ L)))
    (hmul : ∀ q q', δ (q * q') = δ q * δ q')
    (hU1 : ∀ q : ↥(c134Q G₀ L), (q : G) ∈ centerOf (c134Q G₀ L) → δ q = 1)
    (hequiv : ∀ (g : ↥L) (q : ↥(c134Q G₀ L)),
      δ (cnj (H.le_normalizer_Q (H.le g.2)) q) = cnj (H.le_normalizer_U (H.le g.2)) (δ q))
    (q : ↥(c134Q G₀ L)) : δ q = 1 := by
  classical
  have hwd : ∀ q q' : ↥(c134Q G₀ L), crd H.dual q = crd H.dual q' → δ q = δ q' := by
    intro q q' h
    have h1 := (crd_eq_iff H.dual q q').mp h
    have e : q' = q * (q⁻¹ * q') := by group
    rw [e, hmul, hU1 _ h1, mul_one]
  have hδ1 : δ 1 = 1 := hU1 1 (Subgroup.one_mem _)
  choose sec hsec using crd_surjective H.dual
  let φ : (Fin 2 → Fin 3 → F) →+ (Fin 3 → F) :=
    { toFun := fun v => crd H.nat (δ (sec v)) 0
      map_zero' := by
        rw [hwd (sec 0) 1 (by rw [hsec, crd_one]), hδ1, crd_one]
        rfl
      map_add' := fun v w => by
        rw [hwd (sec (v + w)) (sec v * sec w) (by rw [hsec, crd_mul, hsec, hsec]), hmul,
          crd_mul]
        rfl }
  have hφ : φ = 0 := by
    refine eq_zero_of_dual_equivariant_pi φ fun γ v => ?_
    obtain ⟨g, hg⟩ := slNat_surjective H.surj.1 γ
    show crd H.nat (δ (sec _)) 0 = _
    have h1 : crd H.dual (cnj (H.le_normalizer_Q (H.le g.2)) (sec v)) =
        dact ((dualHom γ : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) v := by
      rw [crd_conj_true H.dual g (sec v) _ rfl, hg, hsec]
    rw [hwd _ (cnj (H.le_normalizer_Q (H.le g.2)) (sec v)) ((hsec _).trans h1.symm), hequiv,
      crd_conj_false H.nat g (δ (sec v)) _ rfl, hg]
    rfl
  have h0 : crd H.nat (δ q) = 0 := by
    have h1 : crd H.nat (δ q) 0 = φ (crd H.dual q) := by
      show crd H.nat (δ q) 0 = crd H.nat (δ (sec (crd H.dual q))) 0
      rw [hwd (sec (crd H.dual q)) q (hsec _)]
    rw [hφ, AddMonoidHom.zero_apply] at h1
    funext i
    rw [Subsingleton.elim i 0, h1]
    rfl
  rw [crd_eq_zero_iff, Subgroup.mem_bot] at h0
  exact Subtype.ext h0

@[expose] def triv : Subgroup G where
  carrier := {x | ∃ hx : x ∈ Subgroup.normalizer (c134Q G₀ L : Set G),
    ∀ q, crd H.dual (cnj hx q) = crd H.dual q}
  one_mem' := ⟨Subgroup.one_mem _, fun q => by
    congr 1
    exact Subtype.ext (by simp [coe_cnj])⟩
  mul_mem' := by
    rintro x y ⟨hx, hx'⟩ ⟨hy, hy'⟩
    refine ⟨Subgroup.mul_mem _ hx hy, fun q => ?_⟩
    rw [cnj_mul_left hx hy, hx', hy']
  inv_mem' := by
    rintro x ⟨hx, hx'⟩
    refine ⟨Subgroup.inv_mem _ hx, fun q => ?_⟩
    have e : q = cnj hx (cnj (Subgroup.inv_mem _ hx) q) :=
      Subtype.ext (by simp only [coe_cnj]; group)
    conv_rhs => rw [e]
    rw [hx']

theorem crd_cnj_triv {x : G} (hx : x ∈ H.triv) (hxN : x ∈ Subgroup.normalizer (c134Q G₀ L : Set G))
    (q : ↥(c134Q G₀ L)) : crd H.dual (cnj hxN q) = crd H.dual q := by
  obtain ⟨hx', h⟩ := hx
  exact h q

theorem le_triv : c134Q G₀ L ≤ H.triv := fun c hc =>
  ⟨H.le_normalizer_Q (H.le (c134Q_le H.norm hc)), fun q =>
    H.crd_conj_Q ⟨c, hc⟩ q _ rfl⟩

theorem mem_triv_of_ker {a : ↥L} (ha : α a = 1) : (a : G) ∈ H.triv :=
  ⟨H.le_normalizer_Q (H.le a.2), fun q => H.crd_conj_ker ha q _ rfl⟩

variable [Finite G]

theorem pCoreOf_L_le : pCoreOf 2 L ≤ pCoreOf 2 G₀ :=
  le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 L).trans H.le)
    (H.norm.trans (normalizer_le_normalizer_pCoreOf 2 L)) (pCoreOf_isPGroup 2 L)

theorem mem_pCoreOf_of_ker {a : ↥L} (ha : α a = 1) : (a : G) ∈ pCoreOf 2 G₀ := by
  have h2 : a ∈ α.ker := ha
  rw [H.surj.2] at h2
  exact H.pCoreOf_L_le ((mem_pCoreOf_iff' a).mpr h2)

theorem crd_cm_ker {t : G} (ht : t ∈ pCoreOf 2 G₀) (htr : t ∈ H.triv) {a : ↥L} (ha : α a = 1) :
    crd H.dual (cm ht a) = 0 := by
  refine eq_zero_of_fixed fun γ => ?_
  obtain ⟨g, hg⟩ := H.ρd_surjective γ
  set w := cm ht a with hw
  have haT := H.mem_pCoreOf_of_ker ha
  set c : ↥(c134Q G₀ L) := cm ht g with hc
  set q : ↥(c134Q G₀ L) := cm haT g with hq
  have h₁ : t⁻¹ * a ∈ H.triv := H.triv.mul_mem (H.triv.inv_mem htr) (H.mem_triv_of_ker ha)
  have h₂ : t⁻¹ * a * t ∈ H.triv := H.triv.mul_mem h₁ htr
  have hN₁ : t⁻¹ * a ∈ Subgroup.normalizer (c134Q G₀ L : Set G) := h₁.1
  have hN₂ : t⁻¹ * a * t ∈ Subgroup.normalizer (c134Q G₀ L : Set G) := h₂.1
  have hgN : (g : G) ∈ Subgroup.normalizer (c134Q G₀ L : Set G) := H.le_normalizer_Q (H.le g.2)
  have e : cnj hgN w = c⁻¹ * cnj hN₁ q * cnj hN₂ c * cnj hN₂ q⁻¹ * w := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_cnj, hw, hc, hq, coe_cm]
    group
  have h3 := crd_conj_true H.dual g w (cnj hgN w) rfl
  rw [e, crd_mul, crd_mul, crd_mul, crd_mul, H.crd_cnj_triv h₁, H.crd_cnj_triv h₂,
    H.crd_cnj_triv h₂, crd_inv, crd_inv] at h3
  rw [show H.ρd g = dualHom (slNat α g) from rfl] at hg
  rw [← hg, ← h3]
  abel

omit [Finite G] in
theorem slNat_eq_one_of_ρd {a : ↥L} (ha : H.ρd a = 1) : α a = 1 := by
  have h1 : slNat α a = 1 := by
    have h2 := congrArg dualHom ha
    rwa [show H.ρd a = dualHom (slNat α a) from rfl, dualHom_dualHom, map_one] at h2
  exact (slNat_eq_one_iff a).mp h1

theorem mem_c134Q_of_triv [CharP F 2] {t : G} (ht : t ∈ pCoreOf 2 G₀) (htr : t ∈ H.triv) :
    t ∈ c134Q G₀ L := by
  obtain ⟨c, hc0, hc1, hcc⟩ := H.scalar
  have hCQ := centralizer_c134Q_eq_centerOf hc0 hc1 hcc H.surj H.le H.norm H.perf H.nat H.cent
  obtain ⟨m, hm⟩ := exists_coboundary hc0 hc1 hcc H.ρd_surjective (H.crd_cm_mul ht)
    (fun a ha => H.crd_cm_ker ht htr (H.slNat_eq_one_of_ρd ha))
  obtain ⟨q₀, hq₀⟩ := crd_surjective H.dual m
  have hq₀P : (q₀ : G) ∈ pCoreOf 2 G₀ := H.c134Q_le_pCoreOf q₀.2
  set t₁ := t * (q₀ : G)⁻¹ with ht₁def
  have ht₁ : t₁ ∈ pCoreOf 2 G₀ := (pCoreOf 2 G₀).mul_mem ht ((pCoreOf 2 G₀).inv_mem hq₀P)
  have ht₁r : t₁ ∈ H.triv := H.triv.mul_mem htr (H.triv.inv_mem (H.le_triv q₀.2))
  have ht₁N : t₁ ∈ Subgroup.normalizer (c134Q G₀ L : Set G) := ht₁r.1
  have ht₁U : ∀ u ∈ centerOf (c134Q G₀ L), t₁ * u = u * t₁ := fun u hu =>
    commute_of_mem_pCoreOf H.surj H.le H.norm H.nat ht₁ hu
  have hs : ∀ y : ↥L, (cm ht₁ y : G) ∈ centerOf (c134Q G₀ L) := by
    intro y
    have hyN : (y : G) ∈ Subgroup.normalizer (c134Q G₀ L : Set G) := H.le_normalizer_Q (H.le y.2)
    have e : cm ht₁ y = q₀ * cm ht y * cnj hyN q₀⁻¹ := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_cnj, coe_cm, ht₁def]
      group
    rw [← crd_eq_zero_iff H.dual, e, crd_mul, crd_mul,
      crd_conj_true H.dual y q₀⁻¹ (cnj hyN q₀⁻¹) rfl,
      crd_inv, dact_neg, hm, hq₀]
    show m + (dact ((H.ρd y : Matrix.SpecialLinearGroup (Fin 3) F) :
      Matrix (Fin 3) (Fin 3) F) m - m) + -dact ((H.ρd y : Matrix.SpecialLinearGroup (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F) m = 0
    abel
  have hδmem : ∀ q : ↥(c134Q G₀ L), t₁ * q * t₁⁻¹ * (q : G)⁻¹ ∈ centerOf (c134Q G₀ L) := by
    intro q
    have h1 := (crd_eq_iff H.dual (cnj ht₁N q) q).mp (H.crd_cnj_triv ht₁r ht₁N q)
    have h2 := conj_mem_centerOf (H.le_normalizer_Q (H.c134Q_le_pCoreOf q.2 |> pCoreOf_le 2 G₀))
      ((centerOf (c134Q G₀ L)).inv_mem h1)
    convert h2 using 1
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_cnj]
    group
  let δ : ↥(c134Q G₀ L) → ↥(centerOf (c134Q G₀ L)) := fun q => ⟨_, hδmem q⟩
  have hδ : ∀ q, ((δ q : ↥(centerOf (c134Q G₀ L))) : G) = t₁ * q * t₁⁻¹ * (q : G)⁻¹ :=
    fun q => rfl
  have hδ1 := H.eq_one_of_equivariant δ
    (fun q q' => by
      apply Subtype.ext
      simp only [hδ, Subgroup.coe_mul]
      have hc := Subgroup.mem_centralizer_iff.mp (hδmem q').2 _ ((c134Q G₀ L).inv_mem q.2)
      calc t₁ * (↑q * ↑q') * t₁⁻¹ * (↑q * ↑q')⁻¹ =
            t₁ * ↑q * t₁⁻¹ * ((t₁ * ↑q' * t₁⁻¹ * (↑q')⁻¹) * (↑q)⁻¹) := by group
        _ = t₁ * ↑q * t₁⁻¹ * ((↑q)⁻¹ * (t₁ * ↑q' * t₁⁻¹ * (↑q')⁻¹)) := by rw [hc]
        _ = t₁ * ↑q * t₁⁻¹ * (↑q)⁻¹ * (t₁ * ↑q' * t₁⁻¹ * (↑q')⁻¹) := by group)
    (fun q hq => by
      apply Subtype.ext
      simp only [hδ, OneMemClass.coe_one]
      rw [ht₁U q hq]
      group)
    (fun g q => by
      apply Subtype.ext
      simp only [hδ, coe_cnj]
      have hsg := hs g
      rw [coe_cm] at hsg
      have hgq : (g : G) * q * (g : G)⁻¹ ∈ c134Q G₀ L :=
        (Subgroup.mem_normalizer_iff.mp (H.le_normalizer_Q (H.le g.2)) q).mp q.2
      have hc := Subgroup.mem_centralizer_iff.mp hsg.2 _ hgq
      have e1 : (g : G) * t₁ * (g : G)⁻¹ = t₁ * (t₁⁻¹ * ↑g * t₁ * (↑g)⁻¹) := by group
      calc t₁ * (↑g * ↑q * (↑g)⁻¹) * t₁⁻¹ * (↑g * ↑q * (↑g)⁻¹)⁻¹ =
            t₁ * ((t₁⁻¹ * ↑g * t₁ * (↑g)⁻¹) * (↑g * ↑q * (↑g)⁻¹) *
              (t₁⁻¹ * ↑g * t₁ * (↑g)⁻¹)⁻¹) * t₁⁻¹ * (↑g * ↑q * (↑g)⁻¹)⁻¹ := by
            rw [← hc]; group
        _ = ↑g * (t₁ * ↑q * t₁⁻¹ * (↑q)⁻¹) * (↑g)⁻¹ := by group)
  have ht₁C : t₁ ∈ G₀ ⊓ Subgroup.centralizer (c134Q G₀ L : Set G) := by
    refine ⟨pCoreOf_le 2 G₀ ht₁, Subgroup.mem_centralizer_iff.mpr fun q hq => ?_⟩
    have h1 := congrArg Subtype.val (hδ1 ⟨q, hq⟩)
    simp only [hδ, OneMemClass.coe_one] at h1
    calc q * t₁ = (t₁ * q * t₁⁻¹ * q⁻¹)⁻¹ * (t₁ * q) := by group
      _ = t₁ * q := by rw [h1, inv_one, one_mul]
  rw [hCQ] at ht₁C
  have e : t = t₁ * q₀ := by rw [ht₁def]; group
  rw [e]
  exact (c134Q G₀ L).mul_mem (centerOf_le' ht₁C) q₀.2

end Hyp135

end CFSG.Quasithin.H13.Ch4.C135

end
