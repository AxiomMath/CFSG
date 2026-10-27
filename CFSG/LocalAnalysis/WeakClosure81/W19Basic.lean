module

public import CFSG.LocalAnalysis.WeakClosure81.W19Defs
public import CFSG.LocalAnalysis.WeakClosure81.SevenOne
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenUniqueMax
public import CFSG.CGT.Timmesfeld75.Cfg214Gen
public import CFSG.CGT.Timmesfeld75.L2Real
public import CFSG.LargeExtraspecial.S9TIXC
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.InvolutionCountingOrderFormula

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

namespace W19Aux

theorem inf_eq_bot_of_isPGroup {p : ℕ} {P Q : Subgroup G} (hp : p.Prime) (hodd : p ≠ 2)
    (hP : IsPGroup p P) (hQ : IsPGroup 2 Q) : P ⊓ Q = ⊥ := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hXp : IsPGroup p ↥(P ⊓ Q) := hP.to_le inf_le_left
  have hT2 : IsPGroup 2 ↥(P ⊓ Q) := hQ.to_le inf_le_right
  obtain ⟨a, ha⟩ := (IsPGroup.iff_card).1 hXp
  obtain ⟨b, hb⟩ := (IsPGroup.iff_card).1 hT2
  have ha0 : a = 0 := by
    by_contra hne
    have hdvd : p ∣ 2 ^ b := by
      rw [← hb, ha]
      exact dvd_pow_self p hne
    have : p ∣ 2 := hp.dvd_of_dvd_pow hdvd
    exact hodd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 this)
  rw [ha0, pow_zero] at ha
  exact Subgroup.eq_bot_of_card_eq _ ha

theorem coe_sup_eq_mul_of_perm {A B : Subgroup G} (hperm : (A : Set G) * B = B * A) :
    ((A ⊔ B : Subgroup G) : Set G) = (A : Set G) * (B : Set G) := by
  rw [Subgroup.sup_eq_closure_mul]
  refine Set.Subset.antisymm (fun x hx => ?_) Subgroup.subset_closure
  induction hx using Subgroup.closure_induction'' with
  | one => exact ⟨1, A.one_mem, 1, B.one_mem, mul_one 1⟩
  | mem _ hx => exact hx
  | inv_mem x hx =>
    obtain ⟨a, ha, b, hb, rfl⟩ := hx
    have h1 : b⁻¹ * a⁻¹ ∈ (B : Set G) * (A : Set G) :=
      Set.mul_mem_mul (B.inv_mem hb) (A.inv_mem ha)
    rw [← hperm] at h1
    simpa [mul_inv_rev] using h1
  | mul x y _ _ hx hy =>
    obtain ⟨a, ha, b, hb, rfl⟩ := hx
    obtain ⟨a', ha', b', hb', rfl⟩ := hy
    have h1 : b * a' ∈ (B : Set G) * (A : Set G) := Set.mul_mem_mul hb ha'
    rw [← hperm] at h1
    obtain ⟨c, hc, d, hd, hcd⟩ := h1
    have hcd' : c * d = b * a' := hcd
    refine ⟨a * c, A.mul_mem ha hc, d * b', B.mul_mem hd hb', ?_⟩
    calc a * c * (d * b') = a * (c * d) * b' := by group
      _ = a * (b * a') * b' := by rw [hcd']
      _ = a * b * (a' * b') := by group

theorem card_sup_of_perm {A B : Subgroup G} (hAB : A ⊓ B = ⊥)
    (hperm : (A : Set G) * B = B * A) :
    Nat.card ↥(A ⊔ B) = Nat.card ↥A * Nat.card ↥B := by
  have hset := coe_sup_eq_mul_of_perm hperm
  have hinj := Subgroup.mul_injective_of_disjoint (disjoint_iff.mpr hAB)
  let f : A × B → ↥(A ⊔ B) := fun q =>
    ⟨q.1 * q.2, Subgroup.mul_mem _ (Subgroup.mem_sup_left q.1.2) (Subgroup.mem_sup_right q.2.2)⟩
  have hf : Function.Bijective f := by
    constructor
    · intro x y hxy
      exact hinj (congrArg Subtype.val hxy)
    · rintro ⟨z, hz⟩
      rw [← SetLike.mem_coe, hset] at hz
      obtain ⟨a, ha, b, hb, rfl⟩ := hz
      exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), rfl⟩
  rw [← Nat.card_prod]
  exact (Nat.card_congr (Equiv.ofBijective f hf)).symm

theorem sup_eq_of_card {A C B : Subgroup G} (hAB : A ≤ B) (hCB : C ≤ B) (hAC : A ⊓ C = ⊥)
    (hcard : Nat.card ↥B = Nat.card ↥A * Nat.card ↥C) : A ⊔ C = B := by
  have hinj := Subgroup.mul_injective_of_disjoint (disjoint_iff.mpr hAC)
  let f : A × C → ↥(A ⊔ C) := fun q =>
    ⟨q.1 * q.2, Subgroup.mul_mem _ (Subgroup.mem_sup_left q.1.2) (Subgroup.mem_sup_right q.2.2)⟩
  have hfinj : Function.Injective f := fun x y hxy => hinj (congrArg Subtype.val hxy)
  have h1 : Nat.card ↥A * Nat.card ↥C ≤ Nat.card ↥(A ⊔ C) := by
    rw [← Nat.card_prod]
    exact Nat.card_le_card_of_injective f hfinj
  exact Subgroup.eq_of_le_of_card_ge (sup_le hAB hCB) (by rw [hcard]; exact h1)

theorem exists_conj_of_isSylowIn' {p : ℕ} [Fact p.Prime] {S S' H : Subgroup G}
    (hS : IsSylowIn p S H) (hS' : IsSylowIn p S' H) :
    ∃ h ∈ H, ∀ x : G, x ∈ S' ↔ h⁻¹ * x * h ∈ S := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (↥H) hS.toSylow hS'.toSylow
  have hg' : MulAut.conj g • (hS.toSylow : Subgroup H) = (hS'.toSylow : Subgroup H) := by
    rw [← Sylow.coe_subgroup_smul (g := g), hg]
  refine ⟨g, g.2, fun x => ?_⟩
  constructor
  · intro hx
    have hxH : x ∈ H := hS'.le hx
    have : (⟨x, hxH⟩ : H) ∈ (hS'.toSylow : Subgroup H) := hx
    rw [← hg', Subgroup.mem_smul_pointwise_iff_exists] at this
    obtain ⟨s, hs, hsx⟩ := this
    have : (g : G)⁻¹ * x * g = (s : G) := by
      have h2 : ((MulAut.conj g • s : H) : G) = x := congrArg Subtype.val hsx
      simp only [MulAut.smul_def, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv] at h2
      rw [← h2]; group
    rw [this]
    exact hs
  · intro hx
    have hxH : (g : G)⁻¹ * x * g ∈ H := hS.le hx
    have hxH' : x ∈ H := by
      have := H.mul_mem (H.mul_mem g.2 hxH) (H.inv_mem g.2)
      simpa [mul_assoc] using this
    have : (⟨x, hxH'⟩ : H) ∈ (hS'.toSylow : Subgroup H) := by
      rw [← hg', Subgroup.mem_smul_pointwise_iff_exists]
      refine ⟨⟨(g : G)⁻¹ * x * g, hxH⟩, hx, ?_⟩
      apply Subtype.ext
      simp only [MulAut.smul_def, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv]
      group
    exact this

theorem conjSubgroup_eq_self_of_mem {M : Subgroup G} {y : G} (hy : y ∈ M) :
    conjSubgroup M y = M := by
  ext x
  rw [mem_conjSubgroup_iff]
  constructor
  · intro h
    have := M.mul_mem (M.mul_mem (M.inv_mem hy) h) hy
    simpa [mul_assoc] using this
  · intro hx
    exact M.mul_mem (M.mul_mem hy hx) (M.inv_mem hy)

theorem coe_mul_eq_of_card {A B L : Subgroup G} (hAL : A ≤ L) (hBL : B ≤ L) (hAB : A ⊓ B = ⊥)
    (hcard : Nat.card ↥L = Nat.card ↥A * Nat.card ↥B) :
    (A : Set G) * (B : Set G) = (L : Set G) := by
  have hinj := Subgroup.mul_injective_of_disjoint (disjoint_iff.mpr hAB)
  let f : A × B → L := fun q => ⟨q.1 * q.2, L.mul_mem (hAL q.1.2) (hBL q.2.2)⟩
  have hfinj : Function.Injective f := fun x y hxy => hinj (congrArg Subtype.val hxy)
  have hbij : Function.Bijective f :=
    hfinj.bijective_of_nat_card_le (by rw [Nat.card_prod, hcard])
  ext z
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact L.mul_mem (hAL ha) (hBL hb)
  · intro hz
    obtain ⟨⟨a, b⟩, hab⟩ := hbij.2 ⟨z, hz⟩
    exact ⟨a, a.2, b, b.2, congrArg Subtype.val hab⟩

theorem isCyclic_of_le' {P S : Subgroup G} (hS : IsCyclic S) (hPS : P ≤ S) : IsCyclic P := by
  have : IsCyclic (P.subgroupOf S) := Subgroup.isCyclic _
  exact (Subgroup.subgroupOfEquivOfLe hPS).isCyclic.mp this

end W19Aux

open W19Aux

namespace Hyp193

variable {D : Data G} {V₀ : Subgroup G} {p : ℕ} {X : Subgroup G}

theorem inf_T_eq_bot (h : Hyp193 D V₀ p X) : X ⊓ D.T = ⊥ :=
  inf_eq_bot_of_isPGroup h.prime h.odd h.isPGroup D.sylowM.isPGroup

theorem coe_sup_eq_mul (h : Hyp193 D V₀ p X) :
    ((X ⊔ D.T : Subgroup G) : Set G) = (X : Set G) * (D.T : Set G) :=
  coe_sup_eq_mul_of_perm h.perm

theorem card_sup (h : Hyp193 D V₀ p X) :
    Nat.card ↥(X ⊔ D.T) = Nat.card ↥X * Nat.card ↥D.T :=
  card_sup_of_perm h.inf_T_eq_bot h.perm

theorem isSylowIn_T (h : Hyp193 D V₀ p X) : IsSylowIn 2 D.T (X ⊔ D.T) := by
  refine ⟨le_sup_right, D.sylowM.isPGroup, ?_⟩
  have h1 := Subgroup.relIndex_mul_card D.T (X ⊔ D.T)
  rw [inf_eq_left.mpr le_sup_right, card_sup h] at h1
  have hpos : 0 < Nat.card ↥D.T := Nat.card_pos
  have h2 : D.T.relIndex (X ⊔ D.T) = Nat.card ↥X := Nat.eq_of_mul_eq_mul_right hpos h1
  rw [h2]
  haveI : Fact p.Prime := ⟨h.prime⟩
  obtain ⟨a, ha⟩ := (IsPGroup.iff_card).1 h.isPGroup
  rw [ha]
  intro hd
  have h3 : 2 ∣ p := Nat.Prime.dvd_of_dvd_pow Nat.prime_two hd
  exact h.odd ((Nat.prime_dvd_prime_iff_eq Nat.prime_two h.prime).1 h3).symm

theorem isSylowIn_X (h : Hyp193 D V₀ p X) : IsSylowIn p X (X ⊔ D.T) := by
  refine ⟨le_sup_left, h.isPGroup, ?_⟩
  have h1 := Subgroup.relIndex_mul_card X (X ⊔ D.T)
  rw [inf_eq_left.mpr le_sup_left, card_sup h] at h1
  have hpos : 0 < Nat.card ↥X := Nat.card_pos
  have h2 : X.relIndex (X ⊔ D.T) = Nat.card ↥D.T := by
    apply Nat.eq_of_mul_eq_mul_right hpos
    rw [h1, mul_comm]
  rw [h2]
  obtain ⟨b, hb⟩ := (IsPGroup.iff_card).1 D.sylowM.isPGroup
  rw [hb]
  intro hd
  have h3 : p ∣ 2 := Nat.Prime.dvd_of_dvd_pow h.prime hd
  exact h.odd ((Nat.prime_dvd_prime_iff_eq h.prime Nat.prime_two).1 h3)

theorem orderOf_eq (h : Hyp193 D V₀ p X) {x : G} (hx : x ∈ X ⊔ D.T) :
    ∃ a b : ℕ, orderOf x = 2 ^ a * p ^ b := by
  haveI : Fact p.Prime := ⟨h.prime⟩
  obtain ⟨a, ha⟩ := (IsPGroup.iff_card).1 h.isPGroup
  obtain ⟨b, hb⟩ := (IsPGroup.iff_card).1 D.sylowM.isPGroup
  have hdvd : orderOf x ∣ Nat.card ↥(X ⊔ D.T) := by
    have h1 := orderOf_dvd_natCard (⟨x, hx⟩ : ↥(X ⊔ D.T))
    rwa [← Subgroup.orderOf_coe] at h1
  rw [card_sup h, ha, hb] at hdvd
  obtain ⟨k₁, k₂, h₁, h₂, hk⟩ := Nat.dvd_mul.1 hdvd
  obtain ⟨j, -, rfl⟩ := (Nat.dvd_prime_pow h.prime).1 h₁
  obtain ⟨i, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h₂
  exact ⟨i, j, by rw [← hk]; ring⟩

theorem exists_conj_le (h : Hyp193 D V₀ p X) {P : Subgroup G} (hPH : P ≤ X ⊔ D.T)
    (hP : IsPGroup p P) : ∃ y ∈ X ⊔ D.T, P ≤ conjSubgroup X y := by
  haveI : Fact p.Prime := ⟨h.prime⟩
  obtain ⟨S, hS, hPS⟩ := exists_isSylowIn_ge p hPH hP
  obtain ⟨g, hg, hgx⟩ := exists_conj_of_isSylowIn' (isSylowIn_X h) hS
  refine ⟨g⁻¹, (X ⊔ D.T).inv_mem hg, fun x hx => ?_⟩
  rw [mem_conjSubgroup_iff]
  have := (hgx x).1 (hPS hx)
  simpa using this

theorem pCoreOf_le_T (h : Hyp193 D V₀ p X) : pCoreOf 2 (X ⊔ D.T) ≤ D.T :=
  E1.pCoreOf_two_le_of_isSylowIn (isSylowIn_T h)

theorem inf_pCoreOf_eq_bot (h : Hyp193 D V₀ p X) : X ⊓ pCoreOf 2 (X ⊔ D.T) = ⊥ :=
  le_bot_iff.1 ((inf_le_inf_left X (pCoreOf_le_T h)).trans h.inf_T_eq_bot.le)

theorem inf_conj_eq_bot (h : Hyp193 D V₀ p X) (hN₀ : D.M ≤ normalizer (V₀ : Set G)) {y : G}
    (hy : y ∈ D.M) {g : G} (hg : g ∉ D.M) (hV₀ : V₀ ≤ conjSubgroup D.M g) :
    conjSubgroup X y ⊓ conjSubgroup D.M g = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  have hx1 : x ∈ conjSubgroup X y := (Subgroup.mem_inf.1 hx).1
  have hx2 : x ∈ conjSubgroup D.M g := (Subgroup.mem_inf.1 hx).2
  rw [mem_conjSubgroup_iff] at hx1 hx2
  have hg' : g * y⁻¹ ∉ D.M := fun hmem => hg (by simpa using D.M.mul_mem hmem hy)
  have hV' : V₀ ≤ conjSubgroup D.M (g * y⁻¹) := by
    intro v hv
    rw [mem_conjSubgroup_iff]
    have hv' : y⁻¹ * v * y ∈ V₀ := by
      have := (Subgroup.mem_normalizer_iff.1 (hN₀ (D.M.inv_mem hy)) v).1 hv
      simpa using this
    have h2 : y⁻¹ * v * y ∈ conjSubgroup D.M g := hV₀ hv'
    rw [mem_conjSubgroup_iff] at h2
    have e : g * y⁻¹ * v * (g * y⁻¹)⁻¹ = g * (y⁻¹ * v * y) * g⁻¹ := by group
    rw [e]
    exact h2
  have hbot := h.inf_eq_bot (g * y⁻¹) hg' hV'
  have hx' : y * x * y⁻¹ ∈ X ⊓ conjSubgroup D.M (g * y⁻¹) := by
    refine Subgroup.mem_inf.2 ⟨hx1, ?_⟩
    rw [mem_conjSubgroup_iff]
    have e : g * y⁻¹ * (y * x * y⁻¹) * (g * y⁻¹)⁻¹ = g * x * g⁻¹ := by group
    rw [e]
    exact hx2
  rw [hbot, Subgroup.mem_bot] at hx'
  rw [conj_eq_one_iff.1 hx']
  exact Subgroup.one_mem _

theorem uniqueMax_of_le_conj (h : Hyp193 D V₀ p X) {y : G} (hy : y ∈ D.M) {Y : Subgroup G}
    (hY : Y ≤ conjSubgroup X y) (hYc : ¬ IsCyclic Y) : UniqueMax D.M Y := by
  have hY' : conjSubgroup Y y⁻¹ ≤ X := by
    intro z hz
    rw [mem_conjSubgroup_iff] at hz
    have h1 := hY hz
    rw [mem_conjSubgroup_iff] at h1
    have e : y * (y⁻¹ * z * y⁻¹⁻¹) * y⁻¹ = z := by group
    rwa [e] at h1
  have hcyc : ¬ IsCyclic ↥(conjSubgroup Y y⁻¹) := by
    intro hc
    apply hYc
    exact (Subgroup.equivMapOfInjective Y (MulAut.conj y⁻¹⁻¹).toMonoidHom
      (MulAut.conj y⁻¹⁻¹).injective).isCyclic.2 hc
  have hU := h.uniqueMax _ hY' hcyc
  have h2 := uniqueMax_conjSubgroup hU y
  rwa [conjSubgroup_eq_self_of_mem hy, conjSubgroup_conjSubgroup, inv_mul_cancel,
    conjSubgroup_one] at h2

theorem inf_conj_M_eq_bot (h : Hyp193 D V₀ p X) (hN₀ : D.M ≤ normalizer (V₀ : Set G))
    {P : Subgroup G} (hPH : P ≤ X ⊔ D.T) (hP : IsPGroup p P) {g : G} (hg : g ∉ D.M)
    (hV₀ : V₀ ≤ conjSubgroup D.M g) : P ⊓ conjSubgroup D.M g = ⊥ := by
  obtain ⟨y, hy, hPy⟩ := exists_conj_le h hPH hP
  have := inf_conj_eq_bot h hN₀ (h.le_M hy) hg hV₀
  exact le_bot_iff.1 ((inf_le_inf_right _ hPy).trans this.le)

theorem isPGroup_two_inf_conj_M (h : Hyp193 D V₀ p X) (hN₀ : D.M ≤ normalizer (V₀ : Set G))
    {g : G} (hg : g ∉ D.M) (hV₀ : V₀ ≤ conjSubgroup D.M g) :
    IsPGroup 2 ↥((X ⊔ D.T) ⊓ conjSubgroup D.M g) := by
  haveI : Fact p.Prime := ⟨h.prime⟩
  set Q : Subgroup G := (X ⊔ D.T) ⊓ conjSubgroup D.M g with hQ
  have hQH : Q ≤ X ⊔ D.T := inf_le_left
  have hdvd : Nat.card ↥Q ∣ Nat.card ↥(X ⊔ D.T) := Subgroup.card_dvd_of_le hQH
  obtain ⟨a, ha⟩ := (IsPGroup.iff_card).1 h.isPGroup
  obtain ⟨b, hb⟩ := (IsPGroup.iff_card).1 D.sylowM.isPGroup
  rw [card_sup h, ha, hb] at hdvd
  have hnp : ¬ p ∣ Nat.card ↥Q := by
    intro hpd
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥Q) p hpd
    have hxQ : (x : G) ∈ Q := x.2
    have hox : orderOf (x : G) = p := by rw [Subgroup.orderOf_coe]; exact hx
    have hP : IsPGroup p (Subgroup.zpowers (x : G)) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hox, pow_one])
    have hxH : Subgroup.zpowers (x : G) ≤ X ⊔ D.T := (Subgroup.zpowers_le).2 (hQH hxQ)
    have hxM : Subgroup.zpowers (x : G) ≤ conjSubgroup D.M g :=
      (Subgroup.zpowers_le).2 (Subgroup.mem_inf.1 hxQ).2
    have hbot : Subgroup.zpowers (x : G) = ⊥ := by
      have h1 := inf_conj_M_eq_bot h hN₀ hxH hP hg hV₀
      rwa [inf_eq_left.2 hxM] at h1
    have hx1 : (x : G) = 1 := by
      have : (x : G) ∈ Subgroup.zpowers (x : G) := Subgroup.mem_zpowers _
      rw [hbot] at this
      exact Subgroup.mem_bot.1 this
    rw [hx1, orderOf_one] at hox
    exact h.prime.one_lt.ne hox
  have hcop : Nat.Coprime (Nat.card ↥Q) (p ^ a) :=
    Nat.Coprime.pow_right a ((Nat.Prime.coprime_iff_not_dvd h.prime).2 hnp).symm
  have hdvd2 : Nat.card ↥Q ∣ 2 ^ b := hcop.dvd_of_dvd_mul_left hdvd
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd2
  exact IsPGroup.of_card hk

end Hyp193

theorem centralizer_le_conj_M {D : Data G} {V₀ V : Subgroup G} (hset : WeakClosureSetting D V₀ V)
    (hV₀ : V₀ ≠ ⊥) (g : G) {w : G} (hw : w ∈ conjSubgroup V₀ g) (hw1 : w ≠ 1) :
    centralizer ({w} : Set G) ≤ conjSubgroup D.M g := by
  have h1 := centralizer_le_normalizer_conj (hset.ti₀ hV₀).1 g hw hw1
  rwa [← CFSG.Quasithin.E3.conjSubgroup_normalizer, hset.normalizer₀ hV₀] at h1

theorem Hyp193.isPGroup_two_inf_centralizer {D : Data G} {V₀ V : Subgroup G} {p : ℕ}
    {X : Subgroup G} (h : Hyp193 D V₀ p X) (hset : WeakClosureSetting D V₀ V) (hV₀ : V₀ ≠ ⊥)
    {g : G} (hg : g ∉ D.M) (hV₀g : V₀ ≤ conjSubgroup D.M g) {w : G}
    (hw : w ∈ conjSubgroup V₀ g) (hw1 : w ≠ 1) :
    IsPGroup 2 ↥((X ⊔ D.T) ⊓ centralizer ({w} : Set G)) :=
  (isPGroup_two_inf_conj_M h (hset.normalizer₀ hV₀).ge hg hV₀g).to_le
    (inf_le_inf_left _ (centralizer_le_conj_M hset hV₀ g hw hw1))

end CFSG.LocalAnalysis.WeakClosure81
