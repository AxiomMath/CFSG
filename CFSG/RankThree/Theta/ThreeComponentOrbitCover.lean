module

public import CFSG.RankThree.Theta.ThreeCoreComponentNormalization
public import CFSG.RankThree.GroupTheory.ThetaComponents
public import CFSG.RankThree.PerfectCover.CentralQuotientPrimeSupport
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.GroupTheory.LocalCores.Layer
public import CFSG.LocalAnalysis.SectionRank.SQT
public import CFSG.LocalAnalysis.SectionRank.SubgroupRank

public section

namespace CFSG.RankThree.Theta

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank Subgroup
open scoped Pointwise
open CFSG.Assembly.RankThreeEven (localRank)

variable {G : Type*} [Group G]

theorem three_pow_card_le_card_ker_pow {M : Type*} [CommGroup M] [Finite M] {ι : Type*}
    [Fintype ι] [DecidableEq ι] (y : ι → M) (hgen : closure (Set.range y) = ⊤)
    (S : ι → Subgroup M) (hS : ∀ i j, i ≠ j → y j ∈ S i) (hSy : ∀ i, y i ∉ S i)
    (hSy3 : ∀ i, y i ^ 3 ∈ S i) :
    3 ^ Fintype.card ι ≤ Nat.card (powMonoidHom 3 : M →* M).ker := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have htop : ∀ i, zpowers (QuotientGroup.mk (s := S i) (y i)) = ⊤ := by
    intro i
    rw [eq_top_iff]
    rintro q -
    obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective q
    have hm : QuotientGroup.mk' (S i) m ∈ (closure (Set.range y)).map (QuotientGroup.mk' (S i)) :=
      mem_map_of_mem _ (hgen ▸ mem_top m)
    rw [MonoidHom.map_closure] at hm
    refine (closure_le _).2 ?_ hm
    rintro _ ⟨_, ⟨j, rfl⟩, rfl⟩
    by_cases hij : j = i
    · subst hij
      exact mem_zpowers _
    · have h1 : QuotientGroup.mk' (S i) (y j) = 1 :=
        (QuotientGroup.eq_one_iff _).2 (hS i j (fun h => hij h.symm))
      rw [SetLike.mem_coe, h1]
      exact one_mem _
  have hcard : ∀ i, Nat.card (M ⧸ S i) = 3 := by
    intro i
    have hord : orderOf (QuotientGroup.mk (s := S i) (y i)) = 3 := by
      apply orderOf_eq_prime
      · rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
        exact hSy3 i
      · rw [Ne, QuotientGroup.eq_one_iff]
        exact hSy i
    rw [← card_top (G := M ⧸ S i), ← htop i, Nat.card_zpowers, hord]
  let χ : M →* ((i : ι) → M ⧸ S i) := MonoidHom.pi fun i => QuotientGroup.mk' (S i)
  have hχy : ∀ i, χ (y i) = Pi.mulSingle i (QuotientGroup.mk (y i)) := by
    intro i
    funext j
    by_cases hij : j = i
    · subst hij
      simp [χ]
    · rw [Pi.mulSingle_eq_of_ne hij]
      exact (QuotientGroup.eq_one_iff _).2 (hS j i hij)
  have hχ : Function.Surjective χ := by
    intro x
    have hk : ∀ i, ∃ k : ℤ, (QuotientGroup.mk (s := S i) (y i)) ^ k = x i := fun i =>
      mem_zpowers_iff.1 (htop i ▸ mem_top (x i))
    choose k hk using hk
    refine ⟨∏ i, y i ^ k i, ?_⟩
    rw [map_prod]
    conv_rhs => rw [← Finset.univ_prod_mulSingle x]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [map_zpow, hχy, ← Pi.mulSingle_zpow, hk]
  have hle : (powMonoidHom 3 : M →* M).range ≤ χ.ker := by
    rintro _ ⟨m, rfl⟩
    rw [MonoidHom.mem_ker, powMonoidHom_apply, map_pow]
    funext i
    have h := pow_card_eq_one' (x := χ m i)
    rw [hcard i] at h
    exact h
  have hker : Nat.card (powMonoidHom 3 : M →* M).ker = (powMonoidHom 3 : M →* M).range.index := by
    have h1 := card_eq_card_quotient_mul_card_subgroup (powMonoidHom 3 : M →* M).ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange _).toEquiv] at h1
    have h2 := card_mul_index (powMonoidHom 3 : M →* M).range
    have hpos : 0 < Nat.card (powMonoidHom 3 : M →* M).range := Nat.card_pos
    nlinarith
  have hχcard : χ.ker.index = 3 ^ Fintype.card ι := by
    rw [index_ker, MonoidHom.range_eq_top.2 hχ, card_top, Nat.card_pi]
    simp [hcard]
  rw [hker, ← hχcard]
  exact Nat.le_of_dvd (Nat.pos_of_ne_zero (index_ne_zero_of_finite)) (index_dvd_of_le hle)

theorem mem_center_iff_mem_centralizer (K : Subgroup G) (m : K) :
    m ∈ center K ↔ (m : G) ∈ centralizer (K : Set G) := by
  rw [← LocalCores.mem_map_center_iff K |>.trans (and_iff_right m.2)]
  exact ⟨fun h => mem_map_of_mem _ h, fun ⟨m', hm', he⟩ => by
    rwa [show m = m' from Subtype.ext he.symm]⟩

theorem map_conj_eq_of_mem_normalizer {L : Subgroup G} {g : G}
    (hg : g ∈ normalizer (L : Set G)) : L.map (MulAut.conj g).toMonoidHom = L := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (mem_normalizer_iff.1 hg x).1 hx
  · intro hy
    refine ⟨g⁻¹ * y * g, ?_, by simp [mul_assoc]⟩
    simpa using (mem_normalizer_iff.1 (inv_mem hg) y).1 hy

theorem mem_normalizer_of_map_conj_le {D : Subgroup G} {g : G}
    (h1 : D.map (MulAut.conj g).toMonoidHom ≤ D) (h2 : D.map (MulAut.conj g⁻¹).toMonoidHom ≤ D) :
    g ∈ normalizer (D : Set G) := by
  rw [mem_normalizer_iff]
  intro y
  refine ⟨fun hy => h1 (mem_map_of_mem _ hy), fun hy => ?_⟩
  have h := h2 (mem_map_of_mem _ hy)
  simpa [mul_assoc] using h

theorem mem_centralizer_sup {H K : Subgroup G} {x : G} (hH : x ∈ centralizer (H : Set G))
    (hK : x ∈ centralizer (K : Set G)) : x ∈ centralizer ((H ⊔ K : Subgroup G) : Set G) := by
  have hle : H ⊔ K ≤ centralizer ({x} : Set G) := sup_le
    (fun h hh => mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 hH h hh))
    (fun h hh => mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 hK h hh))
  exact mem_centralizer_iff.2 fun h hh => mem_centralizer_singleton_iff.1 (hle hh)

theorem apply_mem_center_iff {H K : Type*} [Group H] [Group K] (e : H ≃* K) (x : H) :
    e x ∈ center K ↔ x ∈ center H := by
  constructor
  · intro h
    rw [mem_center_iff] at h ⊢
    intro g
    apply e.injective
    rw [map_mul, map_mul]
    exact h (e g)
  · intro h
    rw [mem_center_iff] at h ⊢
    intro g
    obtain ⟨g, rfl⟩ := e.surjective g
    rw [← map_mul, ← map_mul, h g]

theorem exists_eq_insert_pair_of_ncard_eq_three {α : Type*} {s : Set α} {a : α} (ha : a ∈ s)
    (hs : s.ncard = 3) : ∃ b c, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ s = {a, b, c} := by
  obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := Set.ncard_eq_three.1 hs
  rcases ha with rfl | rfl | rfl
  · exact ⟨y, z, hxy, hxz, hyz, rfl⟩
  · exact ⟨x, z, hxy.symm, hyz, hxz, Set.insert_comm _ _ _⟩
  · refine ⟨x, y, hxz.symm, hyz.symm, hxy, ?_⟩
    ext t
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto

section TripleProduct

variable {L L₁ L₂ : Subgroup G} (c10 : L₁ ≤ centralizer (L : Set G))
  (c20 : L₂ ≤ centralizer (L : Set G)) (c21 : L₂ ≤ centralizer (L₁ : Set G))

@[expose] def tripleMul : L × L₁ × L₂ →* (L ⊔ L₁ ⊔ L₂ : Subgroup G) :=
  MonoidHom.codRestrict (L.subtype.noncommCoprod (L₁.subtype.noncommCoprod L₂.subtype
      fun m n => mem_centralizer_iff.1 (c21 n.2) m m.2)
    fun a bc => mem_centralizer_iff.1
      (mul_mem (c10 bc.1.2) (c20 bc.2.2) : (bc.1 : G) * bc.2 ∈ centralizer (L : Set G)) a a.2)
    _ fun x => mul_mem (mem_sup_left (mem_sup_left x.1.2))
      (mul_mem (mem_sup_left (mem_sup_right x.2.1.2)) (mem_sup_right x.2.2.2))

include c10 c20 c21 in
theorem coe_tripleMul (l : L × L₁ × L₂) :
    (tripleMul c10 c20 c21 l : G) = l.1 * l.2.1 * l.2.2 := by
  rw [mul_assoc]
  rfl

include c10 c20 c21 in
theorem tripleMul_surjective : Function.Surjective (tripleMul c10 c20 c21) := by
  have c01 : L ≤ centralizer (L₁ : Set G) := le_centralizer_iff.1 c10
  have c02 : L ≤ centralizer (L₂ : Set G) := le_centralizer_iff.1 c20
  have c12 : L₁ ≤ centralizer (L₂ : Set G) := le_centralizer_iff.1 c21
  have h1 : ((L ⊔ L₁ : Subgroup G) : Set G) = (L : Set G) * (L₁ : Set G) :=
    coe_mul_of_right_le_normalizer_left L L₁ (c10.trans (centralizer_le_normalizer _))
  have h2 : ((L ⊔ L₁ ⊔ L₂ : Subgroup G) : Set G) =
      ((L ⊔ L₁ : Subgroup G) : Set G) * (L₂ : Set G) :=
    coe_mul_of_right_le_normalizer_left _ L₂
      ((le_centralizer_iff.1 (sup_le c02 c12)).trans (centralizer_le_normalizer _))
  rintro ⟨d, hd⟩
  have hd' : d ∈ ((L ⊔ L₁ ⊔ L₂ : Subgroup G) : Set G) := hd
  rw [h2] at hd'
  obtain ⟨x, hx, l₂, hl₂, rfl⟩ := hd'
  rw [SetLike.mem_coe, ← SetLike.mem_coe, h1] at hx
  obtain ⟨l₀, hl₀, l₁, hl₁, rfl⟩ := hx
  exact ⟨(⟨l₀, hl₀⟩, ⟨l₁, hl₁⟩, ⟨l₂, hl₂⟩), Subtype.ext (by rw [coe_tripleMul])⟩

include c10 c20 c21 in
theorem coe_tripleMul_mem_centralizer_iff (l : L × L₁ × L₂) :
    (tripleMul c10 c20 c21 l : G) ∈ centralizer ((L ⊔ L₁ ⊔ L₂ : Subgroup G) : Set G) ↔
      (l.1 : G) ∈ centralizer (L : Set G) ∧ (l.2.1 : G) ∈ centralizer (L₁ : Set G) ∧
        (l.2.2 : G) ∈ centralizer (L₂ : Set G) := by
  have c01 : L ≤ centralizer (L₁ : Set G) := le_centralizer_iff.1 c10
  have c02 : L ≤ centralizer (L₂ : Set G) := le_centralizer_iff.1 c20
  have c12 : L₁ ≤ centralizer (L₂ : Set G) := le_centralizer_iff.1 c21
  obtain ⟨⟨l₀, h₀⟩, ⟨l₁, h₁⟩, ⟨l₂, h₂⟩⟩ := l
  rw [coe_tripleMul]
  simp only
  constructor
  · intro hx
    have hx0 : l₀ * l₁ * l₂ ∈ centralizer (L : Set G) :=
      centralizer_le (le_sup_left.trans le_sup_left : L ≤ L ⊔ L₁ ⊔ L₂) hx
    have hx1 : l₀ * l₁ * l₂ ∈ centralizer (L₁ : Set G) :=
      centralizer_le (le_sup_right.trans le_sup_left : L₁ ≤ L ⊔ L₁ ⊔ L₂) hx
    have hx2 : l₀ * l₁ * l₂ ∈ centralizer (L₂ : Set G) :=
      centralizer_le (le_sup_right : L₂ ≤ L ⊔ L₁ ⊔ L₂) hx
    refine ⟨?_, ?_, ?_⟩
    · have h := mul_mem (mul_mem hx0 (inv_mem (c20 h₂))) (inv_mem (c10 h₁))
      rwa [show l₀ * l₁ * l₂ * l₂⁻¹ * l₁⁻¹ = l₀ by group] at h
    · have h := mul_mem (mul_mem (inv_mem (c01 h₀)) hx1) (inv_mem (c21 h₂))
      rwa [show l₀⁻¹ * (l₀ * l₁ * l₂) * l₂⁻¹ = l₁ by group] at h
    · have h := mul_mem (mul_mem (inv_mem (c12 h₁)) (inv_mem (c02 h₀))) hx2
      rwa [show l₁⁻¹ * l₀⁻¹ * (l₀ * l₁ * l₂) = l₂ by group] at h
  · rintro ⟨hc0, hc1, hc2⟩
    have hm : ∀ x : G, x ∈ centralizer (L : Set G) → x ∈ centralizer (L₁ : Set G) →
        x ∈ centralizer (L₂ : Set G) →
        x ∈ centralizer ((L ⊔ L₁ ⊔ L₂ : Subgroup G) : Set G) := fun x a b c =>
      mem_centralizer_sup (mem_centralizer_sup a b) c
    exact mul_mem (mul_mem (hm _ hc0 (c01 h₀) (c02 h₀)) (hm _ (c10 h₁) hc1 (c12 h₁)))
      (hm _ (c20 h₂) (c21 h₂) hc2)

include c10 c20 c21 in
theorem map_center_sup_three :
    (center (L ⊔ L₁ ⊔ L₂ : Subgroup G)).map (L ⊔ L₁ ⊔ L₂).subtype =
      (center L).map L.subtype ⊔ (center L₁).map L₁.subtype ⊔ (center L₂).map L₂.subtype := by
  have c01 : L ≤ centralizer (L₁ : Set G) := le_centralizer_iff.1 c10
  have c02 : L ≤ centralizer (L₂ : Set G) := le_centralizer_iff.1 c20
  have c12 : L₁ ≤ centralizer (L₂ : Set G) := le_centralizer_iff.1 c21
  apply le_antisymm
  · rintro _ ⟨d, hd, rfl⟩
    obtain ⟨l, rfl⟩ := tripleMul_surjective c10 c20 c21 d
    have h := (coe_tripleMul_mem_centralizer_iff c10 c20 c21 l).1
      ((mem_center_iff_mem_centralizer _ _).1 hd)
    change (tripleMul c10 c20 c21 l : G) ∈ _
    rw [coe_tripleMul]
    exact mul_mem (mul_mem (mem_sup_left (mem_sup_left
      ((LocalCores.mem_map_center_iff L).2 ⟨l.1.2, h.1⟩)))
      (mem_sup_left (mem_sup_right ((LocalCores.mem_map_center_iff L₁).2 ⟨l.2.1.2, h.2.1⟩))))
      (mem_sup_right ((LocalCores.mem_map_center_iff L₂).2 ⟨l.2.2.2, h.2.2⟩))
  · have hD : ∀ x : G, x ∈ L ⊔ L₁ ⊔ L₂ → x ∈ centralizer (L : Set G) →
        x ∈ centralizer (L₁ : Set G) → x ∈ centralizer (L₂ : Set G) →
        x ∈ (center (L ⊔ L₁ ⊔ L₂ : Subgroup G)).map (L ⊔ L₁ ⊔ L₂).subtype := fun x hx a b c =>
      (LocalCores.mem_map_center_iff _).2 ⟨hx, mem_centralizer_sup (mem_centralizer_sup a b) c⟩
    refine sup_le (sup_le ?_ ?_) ?_ <;> intro x hx <;>
      obtain ⟨hxK, hxc⟩ := (LocalCores.mem_map_center_iff _).1 hx
    · exact hD x (mem_sup_left (mem_sup_left hxK)) hxc (c01 hxK) (c02 hxK)
    · exact hD x (mem_sup_left (mem_sup_right hxK)) (c10 hxK) hxc (c12 hxK)
    · exact hD x (mem_sup_right hxK) (c20 hxK) (c21 hxK) hxc

include c10 c20 c21 in
theorem ker_tripleMul_le :
    (tripleMul c10 c20 c21).ker ≤ (center L).prod ((center L₁).prod (center L₂)) := by
  intro l hl
  have h1 : (tripleMul c10 c20 c21 l : G) = 1 := congrArg Subtype.val (MonoidHom.mem_ker.1 hl)
  have h := (coe_tripleMul_mem_centralizer_iff c10 c20 c21 l).1 (by rw [h1]; exact one_mem _)
  exact ⟨(mem_center_iff_mem_centralizer L _).2 h.1,
    (mem_center_iff_mem_centralizer L₁ _).2 h.2.1, (mem_center_iff_mem_centralizer L₂ _).2 h.2.2⟩

include c10 c20 c21 in
theorem exists_quotient_center_mulEquiv (e₁ : L₁ ≃* L) (e₂ : L₂ ≃* L) :
    ∃ ψ : (L ⊔ L₁ ⊔ L₂ : Subgroup G) ⧸ center (L ⊔ L₁ ⊔ L₂ : Subgroup G) ≃*
        (L ⧸ center L) × (L ⧸ center L) × (L ⧸ center L),
      ∀ l : L × L₁ × L₂, ψ (QuotientGroup.mk (tripleMul c10 c20 c21 l)) =
        (QuotientGroup.mk l.1, QuotientGroup.mk (e₁ l.2.1), QuotientGroup.mk (e₂ l.2.2)) := by
  set μ := tripleMul c10 c20 c21 with hμ
  let ν : L × L₁ × L₂ →* (L ⧸ center L) × (L ⧸ center L) × (L ⧸ center L) :=
    (QuotientGroup.mk' (center L)).prodMap
      (((QuotientGroup.mk' (center L)).comp e₁.toMonoidHom).prodMap
        ((QuotientGroup.mk' (center L)).comp e₂.toMonoidHom))
  have hν : Function.Surjective ν := by
    rintro ⟨t₀, t₁, t₂⟩
    obtain ⟨x₀, rfl⟩ := QuotientGroup.mk_surjective t₀
    obtain ⟨x₁, rfl⟩ := QuotientGroup.mk_surjective t₁
    obtain ⟨x₂, rfl⟩ := QuotientGroup.mk_surjective t₂
    refine ⟨(x₀, e₁.symm x₁, e₂.symm x₂), ?_⟩
    change (QuotientGroup.mk x₀, QuotientGroup.mk (e₁ (e₁.symm x₁)),
      QuotientGroup.mk (e₂ (e₂.symm x₂))) = _
    rw [MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
  let μ' := (QuotientGroup.mk' (center (L ⊔ L₁ ⊔ L₂ : Subgroup G))).comp μ
  have hμ' : Function.Surjective μ' :=
    (QuotientGroup.mk'_surjective _).comp (tripleMul_surjective c10 c20 c21)
  have hker : μ'.ker = ν.ker := by
    ext l
    have hνl : ν l = 1 ↔ l.1 ∈ center L ∧ l.2.1 ∈ center L₁ ∧ l.2.2 ∈ center L₂ := by
      rw [show ν l = (QuotientGroup.mk l.1, QuotientGroup.mk (e₁ l.2.1),
          QuotientGroup.mk (e₂ l.2.2)) from rfl, Prod.mk_eq_one, Prod.mk_eq_one,
        QuotientGroup.eq_one_iff, QuotientGroup.eq_one_iff, QuotientGroup.eq_one_iff,
        apply_mem_center_iff, apply_mem_center_iff]
    have hμl : μ' l = 1 ↔ l.1 ∈ center L ∧ l.2.1 ∈ center L₁ ∧ l.2.2 ∈ center L₂ := by
      rw [show μ' l = (QuotientGroup.mk (μ l) : _ ⧸ center (L ⊔ L₁ ⊔ L₂ : Subgroup G)) from rfl,
        QuotientGroup.eq_one_iff, mem_center_iff_mem_centralizer,
        coe_tripleMul_mem_centralizer_iff, mem_center_iff_mem_centralizer,
        mem_center_iff_mem_centralizer, mem_center_iff_mem_centralizer]
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, hμl, hνl]
  refine ⟨(QuotientGroup.quotientKerEquivOfSurjective μ' hμ').symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hker).trans
      (QuotientGroup.quotientKerEquivOfSurjective ν hν)), fun l => ?_⟩
  have h1 : (QuotientGroup.quotientKerEquivOfSurjective μ' hμ').symm (QuotientGroup.mk (μ l)) =
      (l : (L × L₁ × L₂) ⧸ μ'.ker) := by
    rw [MulEquiv.symm_apply_eq]
    rfl
  rw [MulEquiv.trans_apply, h1, MulEquiv.trans_apply, QuotientGroup.quotientMulEquivOfEq_mk]
  rfl

end TripleProduct

theorem map_conjugate_eq (L : Subgroup G) (a : G) :
    (conjugate L a).map (MulAut.conj a : G →* G) = L := by
  ext y
  simp only [conjugate, mem_map, MulEquiv.coe_toMonoidHom, MonoidHom.coe_ofClass,
    MulAut.conj_apply]
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    simpa [mul_assoc] using hx
  · intro hy
    exact ⟨a⁻¹ * y * a, ⟨y, hy, by simp⟩, by simp [mul_assoc]⟩

@[expose] noncomputable def conjugateEquiv (L : Subgroup G) (a : G) : conjugate L a ≃* L :=
  (MulEquiv.subgroupMap (MulAut.conj a) (conjugate L a)).trans
    (MulEquiv.subgroupCongr (map_conjugate_eq L a))

theorem coe_conjugateEquiv (L : Subgroup G) (a : G) (l : conjugate L a) :
    (conjugateEquiv L a l : G) = a * l * a⁻¹ := by
  simp [conjugateEquiv]

@[reducible, expose] def conjAction (A : Subgroup G) : MulAction A (Subgroup G) where
  smul a K := K.map (MulAut.conj (a : G)).toMonoidHom
  one_smul K := by
    change K.map (MulAut.conj ((1 : A) : G)).toMonoidHom = K
    ext y
    simp
  mul_smul a b K := by
    change K.map (MulAut.conj ((a * b : A) : G)).toMonoidHom =
      (K.map (MulAut.conj (b : G)).toMonoidHom).map (MulAut.conj (a : G)).toMonoidHom
    rw [map_map]
    congr 1
    ext g
    simp [mul_assoc]

variable [Finite G]

theorem localRank_le_twoLocalOddRank {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpG : p ∣ Nat.card G) : localRank p G ≤ twoLocalOddRank G := by
  have hbridge : ∀ (q : ℕ) (H : Subgroup G), pRank q H = Open.pRank q H := fun q H =>
    (SectionRank.pRank_eq_open_pRank_top q H).trans (SectionRank.pRank_eq_pRank_top_subgroup H).symm
  have hbdd : BddAbove {r : ℕ | ∃ H : Subgroup G, IsPLocal 2 H ∧
      ∃ q : ℕ, q.Prime ∧ q ≠ 2 ∧ q ∣ Nat.card G ∧ r = pRank q H} := by
    refine ⟨Nat.card G, ?_⟩
    rintro _ ⟨H, -, q, hq, -, -, rfl⟩
    rw [hbridge]
    obtain ⟨E, -, -, hE⟩ := SectionRank.exists_pRank hq.one_lt H
    have h1 : Open.pRank q H < q ^ Open.pRank q H := Nat.lt_pow_self hq.one_lt
    have h2 : Nat.card E ≤ Nat.card G := card_le_card_group E
    omega
  refine csSup_le' ?_
  rintro _ ⟨H, ⟨P, hP, hP2, rfl⟩, rfl⟩
  exact le_csSup hbdd ⟨_, ⟨P, hP, hP2, rfl⟩, p, hp, hp2, hpG, (hbridge p _).symm⟩

theorem card_le_localRank_three {ι : Type*} [Fintype ι] [DecidableEq ι] (K : ι → Subgroup G)
    (hK : ∀ i j, i ≠ j → K j ≤ centralizer (K i : Set G)) (y : ι → G) (hyK : ∀ i, y i ∈ K i)
    (hy : ∀ i, y i ∉ centralizer (K i : Set G)) (hy3 : ∀ i, y i ^ 3 ∈ centralizer (K i : Set G))
    {u : G} (hu : orderOf u = 2) (hyu : ∀ i, y i ∈ centralizer ({u} : Set G)) :
    Fintype.card ι ≤ localRank 3 G := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hpair : (Set.range y).Pairwise Commute := by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ hij
    have hij' : i ≠ j := fun h => hij (h ▸ rfl)
    exact mem_centralizer_iff.1 (hK i j hij' (hyK j)) (y i) (hyK i)
  have hYc : IsMulCommutative (closure (Set.range y)) := isMulCommutative_closure hpair
  have hcomm : ∀ a b : closure (Set.range y), a * b = b * a := fun a b => mul_comm' a b
  let : CommGroup (closure (Set.range y)) :=
    { (inferInstance : Group (closure (Set.range y))) with mul_comm := hcomm }
  let y' : ι → closure (Set.range y) := fun i => ⟨y i, subset_closure ⟨i, rfl⟩⟩
  have hgen : closure (Set.range y') = ⊤ := by
    rw [eq_top_iff, ← closure_closure_coe_preimage (k := Set.range y)]
    refine closure_mono ?_
    rintro x ⟨i, hi⟩
    exact ⟨i, Subtype.ext hi⟩
  have hbound := three_pow_card_le_card_ker_pow y' hgen
    (fun i => (centralizer (K i : Set G)).subgroupOf (closure (Set.range y)))
    (fun i j hij => mem_subgroupOf.2 (hK i j hij (hyK j))) (fun i h => hy i (mem_subgroupOf.1 h))
    (fun i => mem_subgroupOf.2 (hy3 i))
  set Ω : Subgroup G := (powMonoidHom 3 : closure (Set.range y) →* _).ker.map
    (closure (Set.range y)).subtype with hΩ
  have hΩcard : Nat.card Ω = Nat.card (powMonoidHom 3 : closure (Set.range y) →* _).ker :=
    card_map_of_injective (closure (Set.range y)).subtype_injective
  have hΩY : Ω ≤ closure (Set.range y) := map_subtype_le _
  have hΩc : IsMulCommutative Ω := ⟨⟨fun a b => Subtype.ext
    (show (a : G) * b = b * a from congrArg Subtype.val (hcomm ⟨a, hΩY a.2⟩ ⟨b, hΩY b.2⟩))⟩⟩
  have hΩq : ∀ w ∈ Ω, w ^ 3 = 1 := by
    rintro _ ⟨m, hm, rfl⟩
    have h := congrArg Subtype.val (MonoidHom.mem_ker.1 hm)
    exact h
  have hΩp : IsPGroup 3 Ω := fun w => ⟨1, Subtype.ext (by
    rw [pow_one, coe_pow, hΩq _ w.2, coe_one])⟩
  obtain ⟨r, hr⟩ := hΩp.exists_card_eq
  have hu1 : u ≠ 1 := fun h => by rw [h, orderOf_one] at hu; omega
  have hU : zpowers u ≠ ⊥ := fun h => hu1 (by
    have : u ∈ zpowers u := mem_zpowers u
    rwa [h, mem_bot] at this)
  have hU2 : IsPGroup 2 (zpowers u) := IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hu,
    pow_one])
  have hYu : closure (Set.range y) ≤ centralizer ({u} : Set G) := (closure_le _).2 (by
    rintro _ ⟨i, rfl⟩
    exact hyu i)
  have hCu : centralizer ({u} : Set G) ≤ normalizer (zpowers u : Set G) := by
    rw [← centralizer_closure, ← zpowers_eq_closure]
    exact centralizer_le_normalizer _
  have hr' := le_localRank_of_le_normalizer (by norm_num) hU hU2 hΩc hΩq hr
    ((hΩY.trans hYu).trans hCu)
  have h3r : 3 ^ Fintype.card ι ≤ 3 ^ r := by
    rw [← hr, hΩcard]
    exact hbound
  have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).1 h3r
  omega

theorem isComponent_of_mem_thetaComponents {p : ℕ} (hp : p.Prime)
    (hθ : aschbacherSolvableCore p G = ⊥) {L : Subgroup G} (hL : L ∈ thetaComponents p G) :
    IsComponent L := by
  have hcore : aschbacherSolvableCore p L = ⊥ := by
    rw [aschbacherSolvableCore_eq_subgroupOf hp hL.2.1, hθ, bot_subgroupOf]
  exact ⟨LocalCores.isQuasisimple_of_mulEquiv
    ((QuotientGroup.quotientMulEquivOfEq hcore).trans QuotientGroup.quotientBot) hL.2.2, hL.2.1⟩

theorem center_map_le_pCore_three (hθ : aschbacherSolvableCore 3 G = ⊥) {K : Subgroup G}
    (hK : IsComponent K) : (center K).map K.subtype ≤ pCore 3 G := by
  have hr : ∀ r : ℕ, r.Prime → r ≠ 3 → pCore r G = ⊥ := fun r hr hr3 => le_bot_iff.1
    (hθ ▸ (solvable_prime_complement_core_characterization Nat.prime_three).2.2.2.2.2.2 r hr hr3)
  have hF : fittingSubgroup G ≤ pCore 3 G := by
    rw [LocalCores.fittingSubgroup_eq_iSup_pCore]
    refine iSup_le fun r => ?_
    by_cases h : (r : ℕ) = 3
    · rw [h]
    · rw [hr r (Nat.prime_of_mem_primeFactors r.2) h]
      exact bot_le
  have : (layer G).Characteristic := LocalCores.layer_characteristic
  set N : Subgroup G := layer G ⊓ centralizer (layer G : Set G) with hN
  have hNc : IsMulCommutative N :=
    ⟨⟨fun a b => Subtype.ext (mem_centralizer_iff.1 b.2.2 a a.2.1)⟩⟩
  have hNF : N ≤ fittingSubgroup G :=
    LocalCores.fitting_characteristic.2.2 N inferInstance inferInstance
  refine le_trans ?_ (hNF.trans hF)
  intro z hz
  exact (LocalCores.mem_map_center_iff (layer G)).1
    (LocalCores.center_component_le_center_layer hK hz)

theorem center_isPGroup_and_dvd (hθ : aschbacherSolvableCore 3 G = ⊥) {K : Subgroup G}
    (hK : IsComponent K) (hZK : center K ≠ ⊥) :
    IsPGroup 3 (center K) ∧ 3 ∣ Nat.card (K ⧸ center K) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hZ : IsPGroup 3 (center K) := by
    have h := (pCore_isPGroup (p := 3) (G := G)).to_le (center_map_le_pCore_three hθ hK)
    exact h.of_equiv ((center K).equivMapOfInjective K.subtype K.subtype_injective).symm
  refine ⟨hZ, ?_⟩
  have : Group.IsPerfect K := hK.1.1
  by_contra h
  have hnd := PerfectCover.perfect_central_quotient_prime_support Nat.prime_three h
  obtain ⟨k, hk⟩ := hZ.exists_card_eq
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [pow_zero, card_eq_one] at hk
    exact hZK hk
  exact hnd ((dvd_pow_self 3 hk0).trans (hk ▸ card_subgroup_dvd_card (center K)))

theorem exists_mem_not_centralizer_cube {K : Subgroup G} (h3 : 3 ∣ Nat.card (K ⧸ center K)) :
    ∃ y ∈ K, y ∉ centralizer (K : Set G) ∧ y ^ 3 ∈ centralizer (K : Set G) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hkc := mem_center_iff_mem_centralizer K
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' 3 h3
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective t
  refine ⟨k, k.2, fun hk => ?_, ?_⟩
  · have h1 : (k : K ⧸ center K) = 1 := (QuotientGroup.eq_one_iff k).2 ((hkc k).2 hk)
    rw [h1, orderOf_one] at ht
    omega
  · have h1 : ((k ^ 3 : K) : K ⧸ center K) = 1 := by
      rw [QuotientGroup.mk_pow, ← ht, pow_orderOf_eq_one]
    exact (hkc _).1 ((QuotientGroup.eq_one_iff _).1 h1)

theorem exists_orderOf_eq_two_of_not_isSolvable {K : Type*} [Group K] [Finite K]
    (hK : ¬ Group.IsSolvable K) : ∃ u : K, orderOf u = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine exists_prime_orderOf_dvd_card' 2 ?_
  by_contra h
  exact hK (CFSG.FeitThompson.isSolvable_of_odd_natCard _ (Nat.odd_iff.2 (Nat.two_dvd_ne_zero.1 h)))


theorem orbit_three_components (hθ : aschbacherSolvableCore 3 G = ⊥)
    (he : twoLocalOddRank G ≤ 3) (hq : ∀ q : ℕ, q.Prime → 3 < q → localRank q G ≤ 2)
    (h3 : pCore 3 G ≠ ⊥) {A : Subgroup G} (hA : IsPGroup 3 A) {L : Subgroup G}
    (hL : L ∈ thetaComponents 3 G) (hLA : ¬ A ≤ normalizer (L : Set G)) :
    letI := conjAction A
    (MulAction.orbit A L).ncard = 3 ∧ IsComponent L ∧
      MulAction.stabilizer A L = (normalizer (L : Set G)).subgroupOf A ∧
      ∀ K ∈ MulAction.orbit A L, IsComponent K ∧ center K ≠ ⊥ ∧ IsPGroup 3 (center K) ∧
        3 ∣ Nat.card (K ⧸ center K) := by
  let := conjAction A
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hLc := isComponent_of_mem_thetaComponents Nat.prime_three hθ hL
  have h3G : 3 ∣ Nat.card G := by
    obtain ⟨n, hn⟩ := (pCore_isPGroup (p := 3) (G := G)).exists_card_eq
    have hn0 : n ≠ 0 := by
      rintro rfl
      rw [pow_zero, card_eq_one] at hn
      exact h3 hn
    exact (dvd_pow_self 3 hn0).trans (hn ▸ card_subgroup_dvd_card _)
  have hrank3 : localRank 3 G ≤ 3 :=
    (localRank_le_twoLocalOddRank Nat.prime_three (by norm_num) h3G).trans he
  have hZL : center L ≠ ⊥ := fun h => hLA
    (normal_three_core_forces_center_free_component_normalization h3 hrank3 hq hA hLc h)
  have hOK : ∀ K ∈ MulAction.orbit A L, IsComponent K ∧ center K ≠ ⊥ ∧ IsPGroup 3 (center K) ∧
      3 ∣ Nat.card (K ⧸ center K) := by
    rintro _ ⟨a, rfl⟩
    have hKc : IsComponent (L.map (MulAut.conj (a : G)).toMonoidHom) :=
      LocalCores.isComponent_map_mulEquiv _ hLc
    have hKZ : center (L.map (MulAut.conj (a : G)).toMonoidHom) ≠ ⊥ := by
      intro h
      apply hZL
      have hcard := Nat.card_congr (Subgroup.centerCongr
        (L.equivMapOfInjective (MulAut.conj (a : G)).toMonoidHom
          (MulAut.conj (a : G)).injective)).toEquiv
      rw [← card_eq_one, hcard, card_eq_one]
      exact h
    exact ⟨hKc, hKZ, center_isPGroup_and_dvd hθ hKc hKZ⟩
  have hstab : MulAction.stabilizer A L = (normalizer (L : Set G)).subgroupOf A := by
    ext a
    rw [MulAction.mem_stabilizer_iff, mem_subgroupOf]
    exact ⟨fun h => mem_normalizer_of_map_conj_eq_self h,
      fun h => map_conj_eq_of_mem_normalizer h⟩
  refine ⟨?_, hLc, hstab, hOK⟩
  have hidx := MulAction.index_stabilizer A L
  obtain ⟨j, hj⟩ := hA.index (MulAction.stabilizer A L)
  have hj0 : j ≠ 0 := by
    rintro rfl
    rw [pow_zero, index_eq_one, hstab] at hj
    apply hLA
    intro a ha
    have h : (⟨a, ha⟩ : A) ∈ (normalizer (L : Set G)).subgroupOf A := hj ▸ mem_top _
    exact mem_subgroupOf.1 h
  have hle : (MulAction.orbit A L).ncard ≤ 4 := by
    classical
    have hLns : ¬ Group.IsSolvable L := by
      have : Nontrivial L := LocalCores.isQuasisimple_nontrivial hLc.1
      have : Group.IsPerfect L := hLc.1.1
      exact Group.IsPerfect.not_isSolvable L
    obtain ⟨u, hu⟩ := exists_orderOf_eq_two_of_not_isSolvable hLns
    let ι := ↥(MulAction.orbit A L \ {L})
    let : Fintype ι := Fintype.ofFinite ι
    have hι : ∀ i : ι, (i : Subgroup G) ∈ MulAction.orbit A L ∧ (i : Subgroup G) ≠ L :=
      fun i => ⟨i.2.1, i.2.2⟩
    have hcomm : ∀ i j : ι, i ≠ j → (j : Subgroup G) ≤ centralizer ((i : Subgroup G) : Set G) := by
      intro i j hij
      have hne : (j : Subgroup G) ≠ i := fun h => hij (Subtype.ext h.symm)
      exact commutator_eq_bot_iff_le_centralizer.1
        ((LocalCores.distinct_components_commute (hOK _ (hι j).1).1 (hOK _ (hι i).1).1).resolve_left
          hne)
    have hiL : ∀ i : ι, (i : Subgroup G) ≤ centralizer (L : Set G) := fun i =>
      commutator_eq_bot_iff_le_centralizer.1
        ((LocalCores.distinct_components_commute (hOK _ (hι i).1).1 hLc).resolve_left (hι i).2)
    have hex : ∀ i : ι, ∃ y ∈ (i : Subgroup G), y ∉ centralizer ((i : Subgroup G) : Set G) ∧
        y ^ 3 ∈ centralizer ((i : Subgroup G) : Set G) := fun i =>
      exists_mem_not_centralizer_cube (hOK _ (hι i).1).2.2.2
    choose y hyK hy hy3 using hex
    have hyu : ∀ i, y i ∈ centralizer ({(u : G)} : Set G) := fun i =>
      mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 (hiL i (hyK i)) u u.2).symm
    have hcard := card_le_localRank_three (fun i : ι => (i : Subgroup G)) hcomm y hyK hy hy3
      (by rw [orderOf_coe, hu]) hyu
    have hι' : Fintype.card ι = (MulAction.orbit A L).ncard - 1 := by
      rw [Fintype.card_eq_nat_card, Nat.card_coe_set_eq,
        Set.ncard_sdiff_singleton_of_mem (MulAction.mem_orbit_self L)]
    omega
  rw [← hidx, hj] at hle ⊢
  rcases j with _ | _ | j
  · exact absurd rfl hj0
  · norm_num
  · exfalso
    have : 9 ≤ 3 ^ (j + 1 + 1) := by
      rw [pow_succ, pow_succ]
      have : 1 ≤ 3 ^ j := Nat.one_le_pow _ _ (by norm_num)
      omega
    omega


theorem theta_free_three_component_orbit_central_cover_reduction
    (hθ : aschbacherSolvableCore 3 G = ⊥) (he : twoLocalOddRank G ≤ 3)
    (hq : ∀ q : ℕ, q.Prime → 3 < q → localRank q G ≤ 2) (h3 : pCore 3 G ≠ ⊥)
    {A : Subgroup G} (hA : IsPGroup 3 A) {L : Subgroup G} (hL : L ∈ thetaComponents 3 G)
    (hLA : ¬ A ≤ normalizer (L : Set G)) :
    ∃ (a₁ a₂ : G) (L₁ L₂ : Subgroup G), a₁ ∈ A ∧ a₂ ∈ A ∧
      L₁ = conjugate L a₁ ∧ L₂ = conjugate L a₂ ∧
      {K | ∃ a ∈ A, K = conjugate L a} = {L, L₁, L₂} ∧ L ≠ L₁ ∧ L ≠ L₂ ∧ L₁ ≠ L₂ ∧
      IsComponent L ∧ IsComponent L₁ ∧ IsComponent L₂ ∧
      (∀ K ∈ ({L, L₁, L₂} : Set (Subgroup G)),
        center K ≠ ⊥ ∧ IsPGroup 3 (center K) ∧ 3 ∣ Nat.card (K ⧸ center K)) ∧
      A ≤ normalizer ((L ⊔ L₁ ⊔ L₂ : Subgroup G) : Set G) ∧
      Group.IsPerfect (L ⊔ L₁ ⊔ L₂ : Subgroup G) ∧
      (center (L ⊔ L₁ ⊔ L₂ : Subgroup G)).map (L ⊔ L₁ ⊔ L₂).subtype =
        (center L).map L.subtype ⊔ (center L₁).map L₁.subtype ⊔ (center L₂).map L₂.subtype ∧
      center (L ⊔ L₁ ⊔ L₂ : Subgroup G) ≠ ⊥ ∧ IsPGroup 3 (center (L ⊔ L₁ ⊔ L₂ : Subgroup G)) ∧
      ∃ μ : L × L₁ × L₂ →* (L ⊔ L₁ ⊔ L₂ : Subgroup G),
        (∀ l, (μ l : G) = l.1 * l.2.1 * l.2.2) ∧ Function.Surjective μ ∧
        (∀ l, l ∈ μ.ker ↔ (l.1 : G) * l.2.1 * l.2.2 = 1) ∧
        μ.ker ≤ (center L).prod ((center L₁).prod (center L₂)) ∧
        μ.ker ≤ center (L × L₁ × L₂) ∧ IsPGroup 3 μ.ker ∧
      ∃ (e₁ : L₁ ≃* L) (e₂ : L₂ ≃* L),
        (∀ l : L₁, (e₁ l : G) = a₁ * l * a₁⁻¹) ∧ (∀ l : L₂, (e₂ l : G) = a₂ * l * a₂⁻¹) ∧
      ∃ ψ : (L ⊔ L₁ ⊔ L₂ : Subgroup G) ⧸ center (L ⊔ L₁ ⊔ L₂ : Subgroup G) ≃*
          (L ⧸ center L) × (L ⧸ center L) × (L ⧸ center L),
        (∀ l : L × L₁ × L₂, ψ (QuotientGroup.mk (μ l)) =
          (QuotientGroup.mk l.1, QuotientGroup.mk (e₁ l.2.1), QuotientGroup.mk (e₂ l.2.2))) ∧
      ∃ σ : A →* Equiv.Perm (Fin 3),
        (∀ (a : A) (i : Fin 3),
          (![L, L₁, L₂] i).map (MulAut.conj (a : G)).toMonoidHom = ![L, L₁, L₂] (σ a i)) ∧
        (∀ i j : Fin 3, ∃ a : A, σ a i = j) ∧
        Nat.card σ.range = 3 ∧ IsCyclic σ.range ∧
        σ.ker = (normalizer (L : Set G)).subgroupOf A ∧
        ((normalizer (L : Set G)).subgroupOf A).index = 3 ∧
        (Nat.card A = 27 → Nat.card ((normalizer (L : Set G)).subgroupOf A) = 9) := by
  let := conjAction A
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hOcard, hLc, hstab, hOK⟩ := orbit_three_components hθ he hq h3 hA hL hLA
  obtain ⟨M₁, M₂, h01, h02, h12, hO⟩ :=
    exists_eq_insert_pair_of_ncard_eq_three (MulAction.mem_orbit_self L) hOcard
  have hM₁O : M₁ ∈ MulAction.orbit A L := by rw [hO]; simp
  have hM₂O : M₂ ∈ MulAction.orbit A L := by rw [hO]; simp
  obtain ⟨b₁, hb₁⟩ := hM₁O
  obtain ⟨b₂, hb₂⟩ := hM₂O
  have hconj : ∀ b : A, b • L = conjugate L ((b : G)⁻¹) := fun b => by
    simp only [conjugate, inv_inv]
    rfl
  have hb₁' : conjugate L ((b₁ : G)⁻¹) = M₁ := (hconj b₁).symm.trans hb₁
  have hb₂' : conjugate L ((b₂ : G)⁻¹) = M₂ := (hconj b₂).symm.trans hb₂
  subst hb₁' hb₂'
  set L₁ := conjugate L ((b₁ : G)⁻¹) with hL₁
  set L₂ := conjugate L ((b₂ : G)⁻¹) with hL₂
  have hL₁O : L₁ ∈ MulAction.orbit A L := ⟨b₁, hconj b₁⟩
  have hL₂O : L₂ ∈ MulAction.orbit A L := ⟨b₂, hconj b₂⟩
  have hOK' : ∀ K ∈ ({L, L₁, L₂} : Set (Subgroup G)), IsComponent K ∧ center K ≠ ⊥ ∧
      IsPGroup 3 (center K) ∧ 3 ∣ Nat.card (K ⧸ center K) := fun K hK => hOK K (hO ▸ hK)
  have hL₁c := (hOK' L₁ (by simp)).1
  have hL₂c := (hOK' L₂ (by simp)).1
  have c10 : L₁ ≤ centralizer (L : Set G) := commutator_eq_bot_iff_le_centralizer.1
    ((LocalCores.distinct_components_commute hL₁c hLc).resolve_left (Ne.symm h01))
  have c20 : L₂ ≤ centralizer (L : Set G) := commutator_eq_bot_iff_le_centralizer.1
    ((LocalCores.distinct_components_commute hL₂c hLc).resolve_left (Ne.symm h02))
  have c21 : L₂ ≤ centralizer (L₁ : Set G) := commutator_eq_bot_iff_le_centralizer.1
    ((LocalCores.distinct_components_commute hL₂c hL₁c).resolve_left (Ne.symm h12))
  have horbit : {K | ∃ a ∈ A, K = conjugate L a} = MulAction.orbit A L := by
    ext K
    constructor
    · rintro ⟨a, ha, rfl⟩
      refine ⟨⟨a⁻¹, inv_mem ha⟩, ?_⟩
      change (⟨a⁻¹, inv_mem ha⟩ : A) • L = _
      rw [hconj]
      simp only [inv_inv]
    · rintro ⟨b, rfl⟩
      exact ⟨(b : G)⁻¹, inv_mem b.2, hconj b⟩
  have hDinv : A ≤ normalizer ((L ⊔ L₁ ⊔ L₂ : Subgroup G) : Set G) := by
    have hmapO : ∀ (b : A) (K : Subgroup G), K ∈ MulAction.orbit A L →
        K.map (MulAut.conj (b : G)).toMonoidHom ≤ L ⊔ L₁ ⊔ L₂ := by
      intro b K hK
      obtain ⟨c, rfl⟩ := hK
      have hbK : b • c • L ∈ MulAction.orbit A L := ⟨b * c, mul_smul b c L⟩
      rw [hO] at hbK
      change (c • L).map (MulAut.conj (b : G)).toMonoidHom ∈ ({L, L₁, L₂} : Set _) at hbK
      rcases hbK with h | h | h <;> rw [h]
      · exact le_sup_left.trans le_sup_left
      · exact le_sup_right.trans le_sup_left
      · exact le_sup_right
    have hmapD : ∀ b : A,
        (L ⊔ L₁ ⊔ L₂).map (MulAut.conj (b : G)).toMonoidHom ≤ L ⊔ L₁ ⊔ L₂ := fun b => by
      rw [Subgroup.map_sup, Subgroup.map_sup]
      exact sup_le (sup_le (hmapO b L (MulAction.mem_orbit_self L)) (hmapO b L₁ hL₁O))
        (hmapO b L₂ hL₂O)
    intro a ha
    exact mem_normalizer_of_map_conj_le (hmapD ⟨a, ha⟩) (hmapD ⟨a⁻¹, inv_mem ha⟩)
  have hperf : Group.IsPerfect (L ⊔ L₁ ⊔ L₂ : Subgroup G) := by
    rw [isPerfect_iff]
    refine le_antisymm (commutator_le_self _) ?_
    have hp : ∀ K : Subgroup G, IsComponent K → K ≤ L ⊔ L₁ ⊔ L₂ →
        K ≤ ⁅L ⊔ L₁ ⊔ L₂, L ⊔ L₁ ⊔ L₂⁆ := fun K hK hKD =>
      calc K = ⁅K, K⁆ := (isPerfect_iff.1 hK.1.1).symm
        _ ≤ _ := commutator_mono hKD hKD
    exact sup_le (sup_le (hp L hLc (le_sup_left.trans le_sup_left))
      (hp L₁ hL₁c (le_sup_right.trans le_sup_left))) (hp L₂ hL₂c le_sup_right)
  have hZD := map_center_sup_three c10 c20 c21
  have hZDne : center (L ⊔ L₁ ⊔ L₂ : Subgroup G) ≠ ⊥ := by
    intro h
    apply (hOK' L (by simp)).2.1
    have h1 : (center L).map L.subtype ≤
        (center (L ⊔ L₁ ⊔ L₂ : Subgroup G)).map (L ⊔ L₁ ⊔ L₂).subtype :=
      hZD ▸ (le_sup_left.trans le_sup_left)
    rw [h, Subgroup.map_bot, le_bot_iff] at h1
    exact (map_eq_bot_iff_of_injective _ L.subtype_injective).1 h1
  have hZDp : IsPGroup 3 (center (L ⊔ L₁ ⊔ L₂ : Subgroup G)) := by
    have hle : (center (L ⊔ L₁ ⊔ L₂ : Subgroup G)).map (L ⊔ L₁ ⊔ L₂).subtype ≤ pCore 3 G := by
      rw [hZD]
      exact sup_le (sup_le (center_map_le_pCore_three hθ hLc) (center_map_le_pCore_three hθ hL₁c))
        (center_map_le_pCore_three hθ hL₂c)
    exact ((pCore_isPGroup (p := 3) (G := G)).to_le hle).of_equiv
      ((center (L ⊔ L₁ ⊔ L₂ : Subgroup G)).equivMapOfInjective _
        (Subgroup.subtype_injective _)).symm
  have hprodp : IsPGroup 3 ((center L).prod ((center L₁).prod (center L₂))) := by
    obtain ⟨i, hi⟩ := (hOK' L (by simp)).2.2.1.exists_card_eq
    obtain ⟨j, hj⟩ := (hOK' L₁ (by simp)).2.2.1.exists_card_eq
    obtain ⟨k, hk⟩ := (hOK' L₂ (by simp)).2.2.1.exists_card_eq
    refine IsPGroup.of_card (n := i + (j + k)) ?_
    rw [Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv, Nat.card_prod,
      Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv, Nat.card_prod, hi, hj, hk, pow_add,
      pow_add]
  have hmem : ∀ i : Fin 3, ![L, L₁, L₂] i ∈ MulAction.orbit A L := by
    intro i
    rw [hO]
    fin_cases i <;> simp
  let f : Fin 3 → MulAction.orbit A L := fun i => ⟨![L, L₁, L₂] i, hmem i⟩
  have hf : Function.Bijective f := by
    constructor
    · intro i j hij
      have h := congrArg Subtype.val hij
      fin_cases i <;> fin_cases j <;> simp_all [f]
    · rintro ⟨K, hK⟩
      rw [hO] at hK
      rcases hK with rfl | rfl | rfl
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
      · exact ⟨2, rfl⟩
  let eqv : Fin 3 ≃ MulAction.orbit A L := Equiv.ofBijective f hf
  let σ : A →* Equiv.Perm (Fin 3) :=
    (Equiv.permCongrHom eqv.symm).toMonoidHom.comp (MulAction.toPermHom A (MulAction.orbit A L))
  have hσ : ∀ (a : A) (i : Fin 3), eqv (σ a i) = a • eqv i := by
    intro a i
    simp [σ, Equiv.permCongrHom_coe, Equiv.permCongr_apply]
  have hσmap : ∀ (a : A) (i : Fin 3),
      (![L, L₁, L₂] i).map (MulAut.conj (a : G)).toMonoidHom = ![L, L₁, L₂] (σ a i) := by
    intro a i
    have h := congrArg Subtype.val (hσ a i)
    exact h.symm
  have hσtrans : ∀ i j : Fin 3, ∃ a : A, σ a i = j := by
    intro i j
    obtain ⟨a, ha⟩ := MulAction.exists_smul_eq A (eqv i) (eqv j)
    exact ⟨a, eqv.injective ((hσ a i).trans ha)⟩
  have hkerle : σ.ker ≤ (normalizer (L : Set G)).subgroupOf A := by
    intro a ha
    rw [← hstab, MulAction.mem_stabilizer_iff]
    have h := hσmap a 0
    rw [show σ a = 1 from ha] at h
    exact h
  have hidx : ((normalizer (L : Set G)).subgroupOf A).index = 3 := by
    rw [← hstab, MulAction.index_stabilizer, hOcard]
  have hrange : Nat.card σ.range = 3 := by
    have h3k : 3 ∣ Nat.card σ.range := by
      have h := index_dvd_of_le hkerle
      rw [hidx, index_ker] at h
      exact h
    obtain ⟨k, hk⟩ := (hA.of_surjective σ.rangeRestrict σ.rangeRestrict_surjective).exists_card_eq
    have h6 : 3 ^ k ∣ 6 := by
      rw [← hk]
      have h := card_subgroup_dvd_card σ.range
      rwa [Nat.card_eq_fintype_card (α := Equiv.Perm (Fin 3)), Fintype.card_perm,
        Fintype.card_fin] at h
    rw [hk] at h3k ⊢
    rcases k with _ | _ | k
    · norm_num at h3k
    · rfl
    · exfalso
      have h9 : 9 ∣ 3 ^ (k + 1 + 1) := ⟨3 ^ k, by ring⟩
      have := Nat.le_of_dvd (by norm_num) (h9.trans h6)
      omega
  have hker : σ.ker = (normalizer (L : Set G)).subgroupOf A := by
    refine eq_of_le_of_card_ge hkerle ?_
    have h1 := card_mul_index σ.ker
    have h2 := card_mul_index ((normalizer (L : Set G)).subgroupOf A)
    rw [index_ker, hrange] at h1
    rw [hidx] at h2
    omega
  refine ⟨(b₁ : G)⁻¹, (b₂ : G)⁻¹, L₁, L₂, inv_mem b₁.2, inv_mem b₂.2, rfl, rfl, horbit.trans hO,
    h01, h02, h12, hLc, hL₁c, hL₂c, fun K hK => (hOK' K hK).2, hDinv, hperf, hZD, hZDne, hZDp,
    tripleMul c10 c20 c21, coe_tripleMul c10 c20 c21, tripleMul_surjective c10 c20 c21,
    fun l => ⟨fun h => by rw [← coe_tripleMul c10 c20 c21 l, MonoidHom.mem_ker.1 h, coe_one],
      fun h => MonoidHom.mem_ker.2 (Subtype.ext (by rw [coe_tripleMul, h, coe_one]))⟩,
    ker_tripleMul_le c10 c20 c21, by
      rw [Subgroup.center_prod, Subgroup.center_prod]
      exact ker_tripleMul_le c10 c20 c21, hprodp.to_le (ker_tripleMul_le c10 c20 c21),
    conjugateEquiv L _, conjugateEquiv L _, coe_conjugateEquiv L _, coe_conjugateEquiv L _, ?_⟩
  obtain ⟨ψ, hψ⟩ := exists_quotient_center_mulEquiv c10 c20 c21 (conjugateEquiv L _)
    (conjugateEquiv L _)
  exact ⟨ψ, hψ, σ, hσmap, hσtrans, hrange, isCyclic_of_prime_card hrange, hker, hidx,
    fun h27 => by
      have h := card_mul_index ((normalizer (L : Set G)).subgroupOf A)
      rw [hidx, h27] at h
      omega⟩

end CFSG.RankThree.Theta
