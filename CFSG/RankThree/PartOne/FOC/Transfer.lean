module

public import CFSG.RankThree.PartOne.FOC.Plane
public import CFSG.RankThree.PartOne.S11c.Sec66Glue
import CFSG.RankThree.PartOne.S11d.LieFieldTransfer
public import CFSG.RankThree.PartOne.Census3.NativeForm
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.RankThree.PartOne

open Subgroup CFSG CFSG.Assembly CFSG.Blueprint
open CFSG.Assembly.LowTwoRank (StatedLieTag)
open CFSG.Assembly.RankThreeEven (localRank)
open CFSG.RankThree.PartOne.Sec66T (fixSub innerAut LocalRankLeTwo LocalRankAut)

namespace FOC

@[expose] def FieldInnerT (p : ℕ) (T : Type) [Group T] [Finite T] : Prop :=
  LocalRankLeTwo p T → ∀ (x : T) (β : MulAut T) (E : Subgroup T),
    x ^ p = 1 → β ^ p = 1 → β x = x → (β ∉ innerAut T → LocalRankAut p T β) →
    IsComponentOf (fixSub β) E → x ∈ Subgroup.normalizer (E : Set T) →
    x ∉ E ⊔ Subgroup.centralizer (E : Set T) →
    (∃ (t : StatedLieTag) (n f : ℕ), 1 ≤ f ∧
      LieModel (↥E ⧸ Subgroup.center ↥E) t n 2 (p * f)) → False

@[expose] def FieldInnerTCat : Prop :=
  ∀ (T : Type) [Group T] [Finite T] (p : ℕ), p.Prime → 5 ≤ p → IsSimpleGroup T →
    (∃ a b : T, a * b ≠ b * a) → Census3.TheoremThreeListNative T → FieldInnerT p T

@[expose] def NoPCenter : ∀ (H : Type) [Group H] [Finite H], ℕ → Subgroup H → Prop :=
  fun _ _ _ p J => ¬ p ∣ Nat.card (Subgroup.center ↥J)

@[expose] def ListSec : ∀ (H : Type) [Group H] [Finite H], ℕ → Subgroup H → Prop :=
  fun _ _ _ _ J => Census3.TheoremThreeListNative (↥J ⧸ Subgroup.center ↥J)

@[expose] def NoPCenterList : ∀ (H : Type) [Group H] [Finite H], ℕ → Subgroup H → Prop :=
  fun H _ _ p J => NoPCenter H p J ∧ ListSec H p J

section Transfer

variable {H : Type} [Group H]

theorem centerQuotientConj_of_centralizer {J : Subgroup H} {z : H}
    (hz : z ∈ Subgroup.centralizer (J : Set H)) :
    centerQuotientConj J ⟨z, Subgroup.centralizer_le_normalizer _ hz⟩ = 1 := by
  have hzn : z ∈ Subgroup.normalizer (J : Set H) := Subgroup.centralizer_le_normalizer _ hz
  ext q
  induction q using QuotientGroup.induction_on with
  | H l =>
    have h1 : centerQuotientConj J ⟨z, hzn⟩ (l : ↥J ⧸ Subgroup.center ↥J) =
        ((⟨z * (l : H) * z⁻¹, (Subgroup.mem_normalizer_iff.mp hzn (l : H)).mp l.2⟩ : ↥J) :
          ↥J ⧸ Subgroup.center ↥J) := rfl
    rw [h1]
    show _ = (l : ↥J ⧸ Subgroup.center ↥J)
    congr 1
    apply Subtype.ext
    show z * (l : H) * z⁻¹ = l
    have := Subgroup.mem_centralizer_iff.1 hz l l.2
    calc z * (l : H) * z⁻¹ = (z * l) * z⁻¹ := rfl
      _ = (l * z) * z⁻¹ := by rw [← this]
      _ = l := by group

theorem centerQuotientConj_mul_eq_conj {J : Subgroup H} {u j z : H} (hu : u ∈ Subgroup.normalizer (J : Set H))
    (hj : j ∈ J) (hz : z ∈ Subgroup.centralizer (J : Set H)) (huj : u = j * z) :
    centerQuotientConj J ⟨u, hu⟩ = MulAut.conj ((⟨j, hj⟩ : ↥J) : ↥J ⧸ Subgroup.center ↥J) := by
  have hjn : j ∈ Subgroup.normalizer (J : Set H) := Subgroup.le_normalizer hj
  have hzn : z ∈ Subgroup.normalizer (J : Set H) := Subgroup.centralizer_le_normalizer _ hz
  have h1 : (⟨u, hu⟩ : Subgroup.normalizer (J : Set H)) = ⟨j, hjn⟩ * ⟨z, hzn⟩ :=
    Subtype.ext huj
  rw [h1, map_mul, centerQuotientConj_of_centralizer hz, mul_one]
  exact Sec66T.centerQuotientConj_of_mem ⟨j, hj⟩

end Transfer

section Component

variable {H : Type} [Group H] [Finite H]

@[expose] noncomputable def toQuot (J E : Subgroup H) (hEJ : E ≤ J) :
    ↥E →* ↥J ⧸ Subgroup.center ↥J :=
  (QuotientGroup.mk' (Subgroup.center ↥J)).comp (Subgroup.inclusion hEJ)

noncomputable abbrev imageOfQ (J E : Subgroup H) (hEJ : E ≤ J) : Subgroup (↥J ⧸ Subgroup.center ↥J) :=
  (toQuot J E hEJ).range

omit [Finite H] in
theorem toQuot_apply {J E : Subgroup H} (hEJ : E ≤ J) (e : ↥E) :
    toQuot J E hEJ e = ((⟨(e : H), hEJ e.2⟩ : ↥J) : ↥J ⧸ Subgroup.center ↥J) := rfl

omit [Finite H] in
theorem toQuot_ker_le_center {J E : Subgroup H} (hEJ : E ≤ J) :
    (toQuot J E hEJ).ker ≤ Subgroup.center ↥E := by
  intro x hx
  have h1 : (⟨(x : H), hEJ x.2⟩ : ↥J) ∈ Subgroup.center ↥J :=
    (QuotientGroup.eq_one_iff _).mp hx
  rw [Subgroup.mem_center_iff]
  intro g
  apply Subtype.ext
  have := Subgroup.mem_center_iff.mp h1 ⟨(g : H), hEJ g.2⟩
  exact congrArg (fun w : ↥J => (w : H)) this

theorem imageOfQ_isComponentOf {p : ℕ} (hp : p.Prime) {J : Subgroup H}
    (hZ : ¬ p ∣ Nat.card (Subgroup.center ↥J)) {v : H} (hvN : v ∈ Subgroup.normalizer (J : Set H))
    (hvp : v ^ p = 1) {E : Subgroup H}
    (hE : IsComponentOf (J ⊓ Subgroup.centralizer ({v} : Set H)) E) :
    IsComponentOf (fixSub (centerQuotientConj J ⟨v, hvN⟩))
      (imageOfQ J E (hE.1.trans inf_le_left)) := by
  classical
  have hEJ : E ≤ J := hE.1.trans inf_le_left
  set β := centerQuotientConj J ⟨v, hvN⟩ with hβ
  obtain ⟨θ, hθs, -, hθv⟩ := Sec66T.exists_fixed_hom hp hZ hvN hvp
  set ε := toQuot J E hEJ with hε
  have hle : imageOfQ J E hEJ ≤ fixSub β := by
    rintro _ ⟨e, rfl⟩
    show β (ε e) = ε e
    rw [hε, toQuot_apply, centerQuotientConj_mk_apply hvN]
    congr 1
    apply Subtype.ext
    show v * (e : H) * v⁻¹ = e
    have hc : v * (e : H) = (e : H) * v :=
      (Subgroup.mem_centralizer_singleton_iff.mp (hE.1 e.2).2).symm
    rw [hc]
    group
  have hq : CFSG.IsQuasisimple ↥(imageOfQ J E hEJ) :=
    CFSG.LocalCores.isQuasisimple_of_surjective hE.2.1 ε.rangeRestrict
      ε.rangeRestrict_surjective (by
        rw [MonoidHom.ker_rangeRestrict]
        exact toQuot_ker_le_center hEJ)
  have hsn : ((imageOfQ J E hEJ).subgroupOf (fixSub β)).IsSubnormal := by
    have h1 := Subgroup.IsSubnormal.map hθs hE.2.2
    have heq : (E.subgroupOf (J ⊓ Subgroup.centralizer ({v} : Set H))).map θ =
        (imageOfQ J E hEJ).subgroupOf (fixSub β) := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        have hxE : (x : H) ∈ E := hx
        show ((θ x : ↥(fixSub β)) : ↥J ⧸ Subgroup.center ↥J) ∈ imageOfQ J E hEJ
        rw [hθv x]
        exact ⟨⟨(x : H), hxE⟩, rfl⟩
      · intro hy
        obtain ⟨e, he⟩ := hy
        refine ⟨⟨(e : H), hEJ e.2, (hE.1 e.2).2⟩, e.2, ?_⟩
        apply Subtype.ext
        rw [hθv]
        exact he
    rw [heq] at h1
    exact h1
  exact ⟨hle, hq, hsn⟩

omit [Finite H] in
theorem mem_centralizer_of_mem_center {J E : Subgroup H} (hEJ : E ≤ J) {k : ↥J}
    (hk : k ∈ Subgroup.center ↥J) : (k : H) ∈ Subgroup.centralizer (E : Set H) := by
  rw [Subgroup.mem_centralizer_iff]
  intro g hg
  have := Subgroup.mem_center_iff.mp hk ⟨g, hEJ hg⟩
  exact congrArg (fun w : ↥J => (w : H)) this

omit [Finite H] in
theorem lieModel_imageOfQ {J E : Subgroup H} (hEJ : E ≤ J) (hEq : CFSG.IsQuasisimple ↥E)
    {t : StatedLieTag} {n m : ℕ} (h : LieModel (↥E ⧸ Subgroup.center ↥E) t n 2 m) :
    LieModel (↥(imageOfQ J E hEJ) ⧸ Subgroup.center ↥(imageOfQ J E hEJ)) t n 2 m := by
  have : Group.IsPerfect ↥E := hEq.1
  obtain ⟨e⟩ := nonempty_centerQuotientEquiv_of_surjective (P := ↥E) inferInstance
    (toQuot J E hEJ).rangeRestrict (toQuot J E hEJ).rangeRestrict_surjective (by
      rw [MonoidHom.ker_rangeRestrict]
      exact toQuot_ker_le_center hEJ)
  exact CFSG.LieType.CurtisTits.lieModel_of_mulEquiv e h

omit [Finite H] in
theorem not_mem_sup_imageOfQ {J E : Subgroup H} (hEJ : E ≤ J) (hEq : CFSG.IsQuasisimple ↥E)
    {u j z : H} (hj : j ∈ J) (hz : z ∈ Subgroup.centralizer (J : Set H)) (huj : u = j * z)
    (huE : u ∈ Subgroup.normalizer (E : Set H))
    (hnot : u ∉ E ⊔ Subgroup.centralizer (E : Set H)) :
    ((⟨j, hj⟩ : ↥J) : ↥J ⧸ Subgroup.center ↥J) ∉
      imageOfQ J E hEJ ⊔
        Subgroup.centralizer (imageOfQ J E hEJ : Set (↥J ⧸ Subgroup.center ↥J)) := by
  classical
  have : Group.IsPerfect ↥E := hEq.1
  intro hmem
  obtain ⟨ebar, hebar, wbar, hwbar, hxw⟩ := PlaneInner.exists_mul_of_mem_sup_centralizer hmem
  obtain ⟨e, rfl⟩ := hebar
  obtain ⟨w₀, rfl⟩ := QuotientGroup.mk_surjective wbar
  have hzE : z ∈ Subgroup.centralizer (E : Set H) :=
    Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hEJ) hz
  have hjN : j ∈ Subgroup.normalizer (E : Set H) := by
    have : j = u * z⁻¹ := by rw [huj]; group
    rw [this]
    exact Subgroup.mul_mem _ huE (Subgroup.inv_mem _
      (Subgroup.centralizer_le_normalizer _ hzE))
  have hk : (⟨j, hj⟩ : ↥J)⁻¹ * (⟨(e : H), hEJ e.2⟩ * w₀) ∈ Subgroup.center ↥J := by
    rw [← QuotientGroup.eq, QuotientGroup.mk_mul, ← toQuot_apply hEJ e]
    exact hxw
  set k : ↥J := (⟨j, hj⟩ : ↥J)⁻¹ * (⟨(e : H), hEJ e.2⟩ * w₀) with hkdef
  have hw₀ : (w₀ : H) = (e : H)⁻¹ * j * (k : H) := by
    have h1 : (⟨(e : H), hEJ e.2⟩ * w₀ : ↥J) = ⟨j, hj⟩ * k := by rw [hkdef]; group
    have h2 : ((⟨(e : H), hEJ e.2⟩ * w₀ : ↥J) : H) = j * (k : H) := congrArg (fun x : ↥J => (x : H)) h1
    have h3 : (e : H) * (w₀ : H) = j * (k : H) := h2
    calc (w₀ : H) = (e : H)⁻¹ * ((e : H) * (w₀ : H)) := by group
      _ = (e : H)⁻¹ * (j * (k : H)) := by rw [h3]
      _ = (e : H)⁻¹ * j * (k : H) := by group
  have hkC : (k : H) ∈ Subgroup.centralizer (E : Set H) := mem_centralizer_of_mem_center hEJ hk
  have hwN : (w₀ : H) ∈ Subgroup.normalizer (E : Set H) := by
    rw [hw₀]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.le_normalizer e.2))
      hjN) (Subgroup.centralizer_le_normalizer _ hkC)
  let φ : ↥E →* ↥E := (E.normalizerMonoidHom ⟨(w₀ : H), hwN⟩).toMonoidHom
  have hφ : ∀ g : ↥E, ((φ g : ↥E) : H) = (w₀ : H) * (g : H) * (w₀ : H)⁻¹ := fun g =>
    Subgroup.normalizerMonoidHom_apply_apply_coe E ⟨(w₀ : H), hwN⟩ g
  have hdisp : ∀ g : ↥E, g⁻¹ * φ g ∈ Subgroup.center ↥E := by
    intro g
    apply toQuot_ker_le_center hEJ
    rw [MonoidHom.mem_ker, map_mul, map_inv, toQuot_apply, toQuot_apply]
    have hφJ : (⟨((φ g : ↥E) : H), hEJ (φ g).2⟩ : ↥J) = w₀ * ⟨(g : H), hEJ g.2⟩ * w₀⁻¹ :=
      Subtype.ext (by rw [hφ]; rfl)
    rw [hφJ]
    have hcomm : (QuotientGroup.mk (⟨(g : H), hEJ g.2⟩ : ↥J) : ↥J ⧸ Subgroup.center ↥J) *
        (w₀ : ↥J ⧸ Subgroup.center ↥J) = (w₀ : ↥J ⧸ Subgroup.center ↥J) *
        (QuotientGroup.mk (⟨(g : H), hEJ g.2⟩ : ↥J) : ↥J ⧸ Subgroup.center ↥J) :=
      Subgroup.mem_centralizer_iff.mp hwbar _ ⟨g, rfl⟩
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, ← QuotientGroup.mk_inv]
    rw [← hcomm]
    simp
  have hid := CFSG.ComponentClassification.PerfectAutomorphisms.hom_eq_id_of_central_displacement
    φ hdisp
  have hwC : (w₀ : H) ∈ Subgroup.centralizer (E : Set H) := by
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    have h1 := congrArg (fun ψ : ↥E →* ↥E => ((ψ ⟨g, hg⟩ : ↥E) : H)) hid
    simp only [hφ, MonoidHom.id_apply] at h1
    calc g * (w₀ : H) = ((w₀ : H) * g * (w₀ : H)⁻¹) * (w₀ : H) := by rw [h1]
      _ = (w₀ : H) * g := by group
  apply hnot
  have hu' : u = (e : H) * ((w₀ : H) * (k : H)⁻¹ * z) := by
    have hjeq : j = (e : H) * (w₀ : H) * (k : H)⁻¹ := by rw [hw₀]; group
    rw [huj, hjeq]
    group
  rw [hu']
  refine Subgroup.mul_mem_sup e.2 ?_
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hwC (Subgroup.inv_mem _ hkC)) hzE

omit [Finite H] in
theorem mem_normalizer_imageOfQ {J E : Subgroup H} (hEJ : E ≤ J) {j : H} (hj : j ∈ J)
    (hjN : j ∈ Subgroup.normalizer (E : Set H)) :
    ((⟨j, hj⟩ : ↥J) : ↥J ⧸ Subgroup.center ↥J) ∈
      Subgroup.normalizer (imageOfQ J E hEJ : Set (↥J ⧸ Subgroup.center ↥J)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · rintro ⟨e, rfl⟩
    have he : j * (e : H) * j⁻¹ ∈ E := (Subgroup.mem_normalizer_iff.mp hjN (e : H)).mp e.2
    refine ⟨⟨j * (e : H) * j⁻¹, he⟩, ?_⟩
    rw [toQuot_apply]
    show _ = ((⟨j, hj⟩ : ↥J) : ↥J ⧸ Subgroup.center ↥J) * (toQuot J E hEJ e) *
      ((⟨j, hj⟩ : ↥J) : ↥J ⧸ Subgroup.center ↥J)⁻¹
    rw [toQuot_apply, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
    congr 1
  · rintro ⟨e, he⟩
    have hj' : j⁻¹ * (e : H) * j⁻¹⁻¹ ∈ E :=
      (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hjN) (e : H)).mp e.2
    refine ⟨⟨j⁻¹ * (e : H) * j⁻¹⁻¹, hj'⟩, ?_⟩
    have hkey : toQuot J E hEJ ⟨j⁻¹ * (e : H) * j⁻¹⁻¹, hj'⟩ =
        ((⟨j, hj⟩ : ↥J) : ↥J ⧸ Subgroup.center ↥J)⁻¹ * toQuot J E hEJ e *
          ((⟨j, hj⟩ : ↥J) : ↥J ⧸ Subgroup.center ↥J) := by
      rw [toQuot_apply, toQuot_apply, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
        ← QuotientGroup.mk_mul]
      congr 1
      apply Subtype.ext
      simp
    rw [hkey, he]
    group

omit [Finite H] in
theorem eq_of_conj_eq {T : Type} [Group T] (hc : Subgroup.center T = ⊥) {a b : T}
    (h : (MulAut.conj a : MulAut T) = MulAut.conj b) : a = b := by
  have h1 : b⁻¹ * a ∈ Subgroup.center T := by
    rw [Subgroup.mem_center_iff]
    intro g
    have h2 := congrArg (fun φ : MulAut T => φ g) h
    simp only [MulAut.conj_apply] at h2
    calc g * (b⁻¹ * a) = b⁻¹ * (b * g * b⁻¹) * a := by group
      _ = b⁻¹ * (a * g * a⁻¹) * a := by rw [h2]
      _ = b⁻¹ * a * g := by group
  rw [hc, Subgroup.mem_bot] at h1
  exact (inv_mul_eq_one.mp h1).symm

omit [Finite H] in
theorem center_eq_bot_of_nonab {T : Type} [Group T] (hT : IsSimpleGroup T)
    (h : ∃ a b : T, a * b ≠ b * a) : Subgroup.center T = ⊥ := by
  have := hT
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center T) with h1 | h1
  · exact h1
  · exfalso
    obtain ⟨a, b, hab⟩ := h
    apply hab
    have : a ∈ Subgroup.center T := by rw [h1]; trivial
    exact (Subgroup.mem_center_iff.mp this b).symm

omit [Finite H] in
theorem conj_aut_apply {T : Type} [Group T] (β : MulAut T) (x : T) :
    (MulAut.conj (β x) : MulAut T) = β * MulAut.conj x * β⁻¹ := by
  ext y
  simp [MulAut.conj_apply]

end Component

theorem fieldInnerPlaneWith_noCenter_of_T (hT : FieldInnerTCat) :
    FieldInnerPlaneWith NoPCenterList := by
  intro H _ _ p J A c u v E hp hp5 hrank hJq hJcat hP hAN hAe hAcard hcA hc1 hcC huA hvA huJ hE
    huE hfl
  classical
  obtain ⟨hZ, hlist⟩ := hP
  have hZ' : ¬ p ∣ Nat.card (Subgroup.center ↥J) := hZ
  have : Fact p.Prime := ⟨hp⟩
  have hAcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hAe.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hApow : ∀ x ∈ A, x ^ p = 1 := fun x hx => elemPow_eq_one_of_isElementaryAbelian x hx
  have huN : u ∈ Subgroup.normalizer (J : Set H) := hAN huA
  have hvN : v ∈ Subgroup.normalizer (J : Set H) := hAN hvA
  have hEJ : E ≤ J := hE.1.trans inf_le_left
  have hEq : CFSG.IsQuasisimple ↥E := hE.2.1
  have hTs : IsSimpleGroup (↥J ⧸ Subgroup.center ↥J) := hJq.2.1
  have hTn : ∃ a b : ↥J ⧸ Subgroup.center ↥J, a * b ≠ b * a := hJq.2.2
  have hcen : Subgroup.center (↥J ⧸ Subgroup.center ↥J) = ⊥ := center_eq_bot_of_nonab hTs hTn
  obtain ⟨j, hj, z, hz, huj⟩ := PlaneInner.exists_mul_of_mem_sup_centralizer huJ
  obtain ⟨hfN, hfnot, -, t, n, f, hf, hmodel⟩ := hfl
  have hzE : z ∈ Subgroup.centralizer (E : Set H) :=
    Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hEJ) hz
  have hjN : j ∈ Subgroup.normalizer (E : Set H) := by
    have : j = u * z⁻¹ := by rw [huj]; group
    rw [this]
    exact Subgroup.mul_mem _ hfN (Subgroup.inv_mem _ (Subgroup.centralizer_le_normalizer _ hzE))
  set β : MulAut (↥J ⧸ Subgroup.center ↥J) := centerQuotientConj J ⟨v, hvN⟩ with hβ
  set x : ↥J ⧸ Subgroup.center ↥J := ((⟨j, hj⟩ : ↥J) : ↥J ⧸ Subgroup.center ↥J) with hx
  have hαu : centerQuotientConj J ⟨u, huN⟩ = MulAut.conj x :=
    centerQuotientConj_mul_eq_conj huN hj hz huj
  have hxp : x ^ p = 1 := by
    have h1 := Sec66T.centerQuotientConj_pow huN (hApow u huA)
    rw [hαu, ← map_pow] at h1
    exact eq_of_conj_eq hcen (by rw [h1, map_one])
  have hcommaut : centerQuotientConj J ⟨u, huN⟩ * β = β * centerQuotientConj J ⟨u, huN⟩ := by
    rw [hβ, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hAcomm u huA v hvA)
  have hβx : β x = x := by
    apply eq_of_conj_eq hcen
    rw [conj_aut_apply]
    rw [hαu] at hcommaut
    rw [← hcommaut]
    group
  have hcp : c ^ p = 1 := hApow c hcA
  have hLR : Sec66T.LocalRankLeTwo p (↥J ⧸ Subgroup.center ↥J) :=
    Sec66T.localRankLeTwo_of_localRank hrank hp hZ hcC hc1 hcp
  have hLRaut : β ∉ innerAut (↥J ⧸ Subgroup.center ↥J) →
      Sec66T.LocalRankAut p (↥J ⧸ Subgroup.center ↥J) β := by
    intro hnot
    have hvJ : v ∉ J ⊔ Subgroup.centralizer (J : Set H) := by
      intro hmem
      obtain ⟨q, hq⟩ := PlaneInner.centerQuotientConj_inner_of_mem_sup hvN hmem
      exact hnot ⟨q, hq.symm⟩
    exact Sec66T.localRankAut_of_localRank hrank hp hZ hvN (hApow v hvA) hvJ hcC hc1 hcp
      (hAcomm v hvA c hcA)
  have hcomp := imageOfQ_isComponentOf hp hZ hvN (hApow v hvA) hE
  have hxN : x ∈ Subgroup.normalizer
      (imageOfQ J E hEJ : Set (↥J ⧸ Subgroup.center ↥J)) :=
    mem_normalizer_imageOfQ hEJ hj hjN
  have hnot := not_mem_sup_imageOfQ hEJ hEq hj hz huj hfN hfnot
  exact hT _ p hp hp5 hTs hTn hlist hLR x β (imageOfQ J E hEJ) hxp
    (Sec66T.centerQuotientConj_pow hvN (hApow v hvA)) hβx hLRaut hcomp hxN hnot
    ⟨t, n, f, hf, lieModel_imageOfQ hEJ hEq hmodel⟩

end FOC

end CFSG.RankThree.PartOne
