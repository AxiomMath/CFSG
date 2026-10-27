module

public import CFSG.RankThree.PartOne.S12.InputsSec15

public section

namespace CFSG.RankThree.PartOne

namespace StrongP

section Conj

variable {H : Type*} [Group H]

abbrev conjSub (g : H) (Y : Subgroup H) : Subgroup H :=
  Y.map (MulAut.conj g).toMonoidHom

theorem mem_conjSub_iff {g x : H} {Y : Subgroup H} : x ∈ conjSub g Y ↔ g⁻¹ * x * g ∈ Y := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hy
  · intro h
    exact ⟨g⁻¹ * x * g, h, by simp [MulAut.conj_apply, mul_assoc]⟩

theorem conjSub_mul {g h : H} {Y : Subgroup H} : conjSub h (conjSub g Y) = conjSub (h * g) Y := by
  ext x
  simp only [mem_conjSub_iff, mul_inv_rev, mul_assoc]

theorem conjSub_inf {g : H} {A B : Subgroup H} :
    conjSub g (A ⊓ B) = conjSub g A ⊓ conjSub g B := by
  ext x
  simp only [mem_conjSub_iff, Subgroup.mem_inf]

theorem card_conjSub {g : H} {Y : Subgroup H} : Nat.card (conjSub g Y) = Nat.card Y :=
  Subgroup.card_map_of_injective (MulAut.conj g).injective

theorem conjSub_one {Y : Subgroup H} : conjSub 1 Y = Y := by
  ext x
  simp

theorem conjSub_eq_top_iff {g : H} {Y : Subgroup H} : conjSub g Y = ⊤ ↔ Y = ⊤ := by
  constructor
  · intro h
    refine eq_top_iff.mpr fun x _ => ?_
    have hx : g * x * g⁻¹ ∈ conjSub g Y := h ▸ Subgroup.mem_top _
    simpa [mem_conjSub_iff, mul_assoc] using hx
  · rintro rfl
    refine eq_top_iff.mpr fun x _ => ?_
    exact mem_conjSub_iff.mpr (Subgroup.mem_top _)

theorem le_conjSub_of_normal {S Y : Subgroup H} [S.Normal] (hSY : S ≤ Y) (g : H) :
    S ≤ conjSub g Y := fun s hs => by
  refine mem_conjSub_iff.mpr (hSY ?_)
  simpa [mul_assoc] using Subgroup.Normal.conj_mem ‹S.Normal› s hs g⁻¹

end Conj

end StrongP

open StrongP

section Basic

variable {H : Type*} [Group H] {p : ℕ} {Y : Subgroup H}

theorem IsStronglyPEmbedded.conj (hY : IsStronglyPEmbedded p Y) (g : H) :
    IsStronglyPEmbedded p (conjSub g Y) := by
  obtain ⟨hne, hdvd, hint⟩ := hY
  refine ⟨fun h => hne (conjSub_eq_top_iff.mp h), by rwa [card_conjSub], fun h hh => ?_⟩
  have hg : g⁻¹ * h * g ∉ Y := fun hy => hh (mem_conjSub_iff.mpr hy)
  have key : conjSub g Y ⊓ conjSub h (conjSub g Y) =
      conjSub g (Y ⊓ conjSub (g⁻¹ * h * g) Y) := by
    rw [conjSub_inf, conjSub_mul, conjSub_mul]
    congr 2
    group
  have hcard : Nat.card (conjSub g Y ⊓ conjSub h (conjSub g Y) : Subgroup H) =
      Nat.card (Y ⊓ conjSub (g⁻¹ * h * g) Y : Subgroup H) := by
    rw [key, card_conjSub]
  rw [hcard]
  exact hint _ hg

theorem IsStronglyPEmbedded.normalizer_le [Fact p.Prime] (hY : IsStronglyPEmbedded p Y)
    {U : Subgroup H} (hU : U ≠ ⊥) (hUp : IsPGroup p U) (hUY : U ≤ Y) :
    Subgroup.normalizer (U : Set H) ≤ Y := by
  intro g hg
  by_contra hgY
  refine hY.2.2 g hgY ?_
  have hUle : U ≤ Y ⊓ conjSub g Y := by
    refine le_inf hUY fun u hu => ?_
    rw [mem_conjSub_iff]
    refine hUY ?_
    have := (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer (U : Set H)).inv_mem hg) u).mp hu
    simpa using this
  have hpU : p ∣ Nat.card U := by
    rcases hUp.card_eq_or_dvd with h | h
    · exact absurd (Subgroup.card_eq_one.mp h) hU
    · exact h
  exact hpU.trans (Subgroup.card_dvd_of_le hUle)

namespace StrongP

theorem centralizer_singleton_le_normalizer_zpowers (x : H) :
    Subgroup.centralizer ({x} : Set H) ≤ Subgroup.normalizer (Subgroup.zpowers x : Set H) := by
  intro c hc
  have hc' : c ∈ Subgroup.centralizer ((Subgroup.zpowers x : Subgroup H) : Set H) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
    exact hc
  have hinv : c⁻¹ ∈ Subgroup.centralizer ((Subgroup.zpowers x : Subgroup H) : Set H) :=
    inv_mem hc'
  have hcomm : ∀ z ∈ Subgroup.zpowers x, c * z * c⁻¹ = z := fun z hz => by
    rw [← Subgroup.mem_centralizer_iff.mp hc' z hz]
    simp
  have hcomm' : ∀ z ∈ Subgroup.zpowers x, c⁻¹ * z * c = z := fun z hz => by
    have := Subgroup.mem_centralizer_iff.mp hinv z hz
    simpa using (by rw [← this]; simp : c⁻¹ * z * c⁻¹⁻¹ = z)
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    rw [hcomm y hy]
    exact hy
  · intro hy
    have h1 := hcomm' _ hy
    have h2 : c⁻¹ * (c * y * c⁻¹) * c = y := by group
    rw [h2] at h1
    rw [h1]
    exact hy

theorem isPGroup_zpowers_of_pow_eq_one {x : H} (hxp : x ^ p = 1) :
    IsPGroup p (Subgroup.zpowers x) := by
  rintro ⟨y, hy⟩
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  refine ⟨1, Subtype.ext ?_⟩
  simp only [pow_one, SubgroupClass.coe_pow, OneMemClass.coe_one]
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hxp, one_zpow]

end StrongP

theorem IsStronglyPEmbedded.centralizer_le [Fact p.Prime] (hY : IsStronglyPEmbedded p Y) {x : H}
    (hx1 : x ≠ 1) (hxp : x ^ p = 1) (hxY : x ∈ Y) :
    Subgroup.centralizer ({x} : Set H) ≤ Y := by
  have hU : Subgroup.zpowers x ≠ ⊥ := by
    rw [Ne, Subgroup.zpowers_eq_bot]
    exact hx1
  exact (centralizer_singleton_le_normalizer_zpowers x).trans
    (hY.normalizer_le hU (isPGroup_zpowers_of_pow_eq_one hxp) (Subgroup.zpowers_le.mpr hxY))

theorem IsStronglyPEmbedded.not_dvd_card_of_normal_le (hY : IsStronglyPEmbedded p Y)
    {S : Subgroup H} [S.Normal] (hSY : S ≤ Y) : ¬ p ∣ Nat.card S := by
  obtain ⟨g, hg⟩ : ∃ g : H, g ∉ Y := by
    by_contra h
    push Not at h
    exact hY.1 (eq_top_iff.mpr fun x _ => h x)
  intro hp
  refine hY.2.2 g hg (hp.trans (Subgroup.card_dvd_of_le ?_))
  exact le_inf hSY (le_conjSub_of_normal hSY g)

variable [Finite H]

theorem IsStronglyPEmbedded.index_modEq [Fact p.Prime] (hY : IsStronglyPEmbedded p Y)
    {Q : Subgroup H} (hQ1 : Q ≠ ⊥) (hQp : IsPGroup p Q) (hQY : Q ≤ Y) :
    Y.index ≡ 1 [MOD p] := by
  have hpQ : p ∣ Nat.card Q := by
    rcases hQp.card_eq_or_dvd with h | h
    · exact absurd (Subgroup.card_eq_one.mp h) hQ1
    · exact h
  have hbase : ∀ x : H ⧸ Y, (∀ q : Q, q • x = x) → x = QuotientGroup.mk 1 := by
    intro x hx
    induction x using QuotientGroup.induction_on with
    | H g =>
      by_cases hg : g ∈ Y
      · exact QuotientGroup.eq.mpr (by simpa using hg)
      · exfalso
        refine hY.2.2 g hg (hpQ.trans (Subgroup.card_dvd_of_le (le_inf hQY ?_)))
        intro q hq
        rw [mem_conjSub_iff]
        have h1 : (QuotientGroup.mk (q⁻¹ * g) : H ⧸ Y) = QuotientGroup.mk g :=
          hx ⟨q⁻¹, Q.inv_mem hq⟩
        have h2 := QuotientGroup.eq.mp h1
        simpa [mul_assoc] using h2
  have hfp : Nat.card (MulAction.fixedPoints Q (H ⧸ Y)) = 1 := by
    rw [Nat.card_eq_one_iff_unique]
    refine ⟨⟨fun a b => Subtype.ext ?_⟩, ⟨⟨QuotientGroup.mk 1, ?_⟩⟩⟩
    · rw [hbase a.1 (fun q => a.2 q), hbase b.1 (fun q => b.2 q)]
    · intro q
      change ((q : H) • (QuotientGroup.mk 1 : H ⧸ Y)) = QuotientGroup.mk 1
      rw [MulAction.Quotient.smul_mk]
      exact (QuotientGroup.eq.mpr (by simpa using hQY q.2))
  have h := hQp.card_modEq_card_fixedPoints (H ⧸ Y)
  rw [hfp] at h
  exact h

theorem IsStronglyPEmbedded.exists_isSylowOf_le [Fact p.Prime] (hY : IsStronglyPEmbedded p Y) :
    ∃ P : Subgroup H, IsSylowOf p P ⊤ ∧ P ≤ Y := by
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hY.2.1
  have hxp : (x : H) ^ p = 1 := by
    have := pow_orderOf_eq_one x
    rw [hx] at this
    simpa using congrArg Subtype.val this
  have hx1 : (x : H) ≠ 1 := by
    intro h
    have : x = 1 := Subtype.ext h
    rw [this, orderOf_one] at hx
    exact (Fact.out : p.Prime).one_lt.ne hx
  have hmod := hY.index_modEq (Q := Subgroup.zpowers (x : H))
    (by rw [Ne, Subgroup.zpowers_eq_bot]; exact hx1) (isPGroup_zpowers_of_pow_eq_one hxp)
    (Subgroup.zpowers_le.mpr x.2)
  have hnd : ¬ p ∣ Y.index := by
    intro hd
    have h1 : (1 : ℕ) ≡ 0 [MOD p] := hmod.symm.trans (Nat.modEq_zero_iff_dvd.mpr hd)
    exact (Fact.out : p.Prime).not_dvd_one (Nat.modEq_zero_iff_dvd.mp h1)
  obtain ⟨Q₀⟩ := (inferInstance : Nonempty (Sylow p ↥Y))
  have hsub : ((Q₀ : Subgroup Y).map Y.subtype).subgroupOf Y = (Q₀ : Subgroup Y) := by
    rw [← Subgroup.comap_subtype]
    exact Subgroup.comap_map_eq_self_of_injective Y.subtype_injective _
  refine ⟨(Q₀ : Subgroup Y).map Y.subtype, ⟨le_top, Q₀.isPGroup'.map Y.subtype, ?_⟩,
    Subgroup.map_subtype_le _⟩
  rw [Subgroup.relIndex_top_right, ← Subgroup.relIndex_mul_index (Subgroup.map_subtype_le _),
    Subgroup.relIndex, hsub]
  intro hd
  rcases (Fact.out : p.Prime).dvd_mul.mp hd with h | h
  · exact Q₀.not_dvd_index h
  · exact hnd h

theorem IsStronglyPEmbedded.exists_conj_ge [Fact p.Prime] (hY : IsStronglyPEmbedded p Y)
    {P : Subgroup H} (hP : IsSylowOf p P ⊤) : ∃ g : H, P ≤ conjSub g Y := by
  obtain ⟨Q, hQ, hQY⟩ := hY.exists_isSylowOf_le
  let P' : Sylow p H := hP.2.1.toSylow (by simpa [Subgroup.relIndex_top_right] using hP.2.2)
  let Q' : Sylow p H := hQ.2.1.toSylow (by simpa [Subgroup.relIndex_top_right] using hQ.2.2)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq H P' Q'
  refine ⟨g⁻¹, fun x hx => ?_⟩
  rw [mem_conjSub_iff]
  have hmem : MulAut.conj g • x ∈ ((g • P' : Sylow p H) : Subgroup H) := by
    rw [Sylow.coe_subgroup_smul]
    exact Subgroup.smul_mem_pointwise_smul x (MulAut.conj g) (P' : Subgroup H)
      (by simpa [P'] using hx)
  rw [hg] at hmem
  have := hQY (by simpa [Q'] using hmem)
  simpa [MulAut.smul_def, MulAut.conj_apply] using this

end Basic

end CFSG.RankThree.PartOne
