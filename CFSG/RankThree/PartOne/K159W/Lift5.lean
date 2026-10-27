module

public import CFSG.RankThree.PartOne.K159W.Defs
public import CFSG.RankThree.PartOne.K159W.Fix5
public import CFSG.RankThree.PartOne.K1510R.ZGen
import CFSG.RankThree.PartOne.S10.EmbeddingFixedResidual
import CFSG.RankThree.PartOne.S10.SelectedPrimeNormalizeThetaComponents

public section

namespace CFSG.RankThree.PartOne.K159W

open CFSG CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.RankThree CFSG.RankThree.LocalRank
  CFSG.RankThree.GroupTheory CFSG.RankThree.PartOne CFSG.RankThree.PartOne.StrongP
  CFSG.RankThree.PartOne.K159F

variable {G : Type} [Group G] [Finite G]

section Lift

theorem exists_lift_elemAbelian_conj {p : ℕ} (hp : p.Prime) {X P₁ : Subgroup G}
    (hP₁ : CFSG.ABGLocalTools.IsSylowOf p (P₁ ⊓ X) X)
    (hθ : ¬ p ∣ Nat.card ↥(aschbacherSolvableCore p ↥X))
    {R : Subgroup (↥X ⧸ aschbacherSolvableCore p ↥X)} (hRexp : ∀ b ∈ R, b ^ p = 1)
    (hRab : ∀ a ∈ R, ∀ b ∈ R, a * b = b * a) :
    ∃ (g : ↥X ⧸ aschbacherSolvableCore p ↥X) (R' : Subgroup G), R' ≤ P₁ ⊓ X ∧
      (∀ b ∈ R', b ^ p = 1) ∧ (∀ a ∈ R', ∀ b ∈ R', a * b = b * a) ∧
      Nat.card R' = Nat.card R ∧
      conjSub g R = (R'.subgroupOf X).map (QuotientGroup.mk' (aschbacherSolvableCore p ↥X)) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  set θ := aschbacherSolvableCore p ↥X with hθdef
  set π := QuotientGroup.mk' θ with hπ
  set T : Subgroup ↥X := (P₁ ⊓ X).subgroupOf X with hT
  obtain ⟨Qs, hQs⟩ := hP₁.exists_sylow_eq_subgroupOf
  have hQsT : (Qs : Subgroup ↥X) = T := hQs
  have hTsyl : IsSylowOf p T ⊤ := by
    refine ⟨le_top, ?_, ?_⟩
    · rw [← hQsT]; exact Qs.isPGroup'
    · rw [Subgroup.relIndex_top_right, ← hQsT]; exact Qs.not_dvd_index
  have hTp : IsPGroup p ↥T := hTsyl.2.1
  have hPbar : IsSylowOf p (T.map π) ⊤ := Sec1511.isSylowOf_map_mk' hTsyl
  have hRp : IsPGroup p ↥R := fun b => ⟨1, Subtype.ext (by simpa using hRexp b b.2)⟩
  obtain ⟨g, hg⟩ := exists_conj_le_sylow hPbar hRp
  set R' : Subgroup (↥X ⧸ θ) := conjSub g R with hR'
  have hR'T : R' ≤ T.map π := hg
  have hR'exp : ∀ b ∈ R', b ^ p = 1 := by
    intro b hb
    rw [hR', mem_conjSub_iff] at hb
    have h1 := hRexp _ hb
    have h2 : (g⁻¹ * b * g) ^ p = g⁻¹ * b ^ p * g := by
      have := conj_pow (a := g⁻¹) (b := b) (i := p)
      rwa [inv_inv] at this
    rw [h2] at h1
    have h3 : b ^ p = g * 1 * g⁻¹ := by
      calc b ^ p = g * (g⁻¹ * b ^ p * g) * g⁻¹ := by group
        _ = g * 1 * g⁻¹ := by rw [h1]
    simpa using h3
  have hR'ab : ∀ a ∈ R', ∀ b ∈ R', a * b = b * a := by
    intro a ha b hb
    rw [hR', mem_conjSub_iff] at ha hb
    have h1 := hRab _ ha _ hb
    calc a * b = g * ((g⁻¹ * a * g) * (g⁻¹ * b * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * b * g) * (g⁻¹ * a * g)) * g⁻¹ := by rw [h1]
      _ = b * a := by group
  set R₀ : Subgroup ↥X := T ⊓ R'.comap π with hR₀
  have hR₀T : R₀ ≤ T := inf_le_left
  have hR₀p : IsPGroup p ↥R₀ := hTp.to_le hR₀T
  have hmap : R₀.map π = R' := by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact hx.2
    · intro r hr
      obtain ⟨t, ht, rfl⟩ := hR'T hr
      exact ⟨t, ⟨ht, hr⟩, rfl⟩
  have hR₀card : Nat.card ↥R₀ = Nat.card ↥R := by
    have h1 := Sec1511.card_map_mk' (O := θ) hR₀p hθ
    rw [← hπ, hmap] at h1
    rw [← h1, hR']
    exact card_conjSub
  have hR₀exp : ∀ b ∈ R₀, b ^ p = 1 := by
    intro b hb
    have hb1 : π b ∈ R' := hb.2
    have h1 : π (b ^ p) = π 1 := by rw [map_pow, hR'exp _ hb1, map_one]
    exact Sec1511.eq_of_mk'_eq hTp hθ (T.pow_mem (hR₀T hb) p) T.one_mem h1
  have hR₀ab : ∀ a ∈ R₀, ∀ b ∈ R₀, a * b = b * a := by
    intro a ha b hb
    have ha1 : π a ∈ R' := ha.2
    have hb1 : π b ∈ R' := hb.2
    have h1 : π (a * b) = π (b * a) := by
      rw [map_mul, map_mul]
      exact hR'ab _ ha1 _ hb1
    exact Sec1511.eq_of_mk'_eq hTp hθ (T.mul_mem (hR₀T ha) (hR₀T hb))
      (T.mul_mem (hR₀T hb) (hR₀T ha)) h1
  have hsub : (R₀.map X.subtype).subgroupOf X = R₀ :=
    Subgroup.comap_map_eq_self_of_injective X.subtype_injective R₀
  refine ⟨g, R₀.map X.subtype, ?_, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact (hR₀T hx : x ∈ T)
  · rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, hR₀exp x hx, map_one]
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, hR₀ab x hx y hy]
  · rw [Subgroup.card_map_of_injective X.subtype_injective, hR₀card]
  · rw [hsub, hmap]

omit [Finite G] in
theorem mem_normalizer_of_subgroupOf' {X E : Subgroup G} (hE : E ≤ X) {n : ↥X}
    (hn : n ∈ Subgroup.normalizer ((E.subgroupOf X : Subgroup ↥X) : Set ↥X)) :
    (n : G) ∈ Subgroup.normalizer (E : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  by_cases hy : y ∈ X
  · have := Subgroup.mem_normalizer_iff.1 hn ⟨y, hy⟩
    simpa [Subgroup.mem_subgroupOf] using this
  · have hy' : y ∉ E := fun h => hy (hE h)
    have hy'' : (n : G) * y * (n : G)⁻¹ ∉ E := by
      intro h
      apply hy
      have h1 := hE h
      have hn' : (n : G) ∈ X := n.2
      have := X.mul_mem (X.mul_mem (X.inv_mem hn') h1) hn'
      simpa [mul_assoc] using this
    exact ⟨fun h => absurd h hy', fun h => absurd h hy''⟩

theorem exists_normalizer_lift {p : ℕ} (hp : p.Prime) {X E : Subgroup G} (θ : Subgroup ↥X)
    [θ.Normal] (hEX : E ≤ X) (hEp : IsPGroup p ↥E) (hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a)
    (hθ : ¬ p ∣ Nat.card ↥θ) {n : ↥X ⧸ θ}
    (hn : n ∈ Subgroup.normalizer
      ((((E.subgroupOf X).map (QuotientGroup.mk' θ) : Subgroup (↥X ⧸ θ))) : Set (↥X ⧸ θ))) :
    ∃ m : ↥X, (m : G) ∈ Subgroup.normalizer (E : Set G) ∧ ∀ e : ↥X, e ∈ E.subgroupOf X →
      QuotientGroup.mk' θ (m * e * m⁻¹) = n * QuotientGroup.mk' θ e * n⁻¹ := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  set π := QuotientGroup.mk' θ with hπ
  set EX : Subgroup ↥X := E.subgroupOf X with hEXdef
  set Eb : Subgroup (↥X ⧸ θ) := EX.map π with hEb
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective θ
  obtain ⟨m₀, hm₀⟩ := hπs n
  set T : Subgroup ↥X := θ ⊔ EX with hT
  have hEXp : IsPGroup p ↥EX := hEp.of_equiv (Subgroup.subgroupOfEquivOfLe hEX).symm
  have hEXsyl : CFSG.ABGLocalTools.IsSylowOf p EX T :=
    Sec15Frattini.isSylowOf_sup_of_coprime hEXp hθ
  have hTmem : ∀ t : ↥X, t ∈ T ↔ π t ∈ Eb := by
    intro t
    constructor
    · intro ht
      obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup_of_normal_left.1 ht
      have hπa : π a = 1 := (QuotientGroup.eq_one_iff a).2 ha
      refine ⟨b, hb, ?_⟩
      rw [map_mul, hπa, one_mul]
    · rintro ⟨b, hb, hbt⟩
      have h1 : b⁻¹ * t ∈ θ :=
        (QuotientGroup.eq_one_iff (b⁻¹ * t)).1
          (by show π (b⁻¹ * t) = 1; rw [map_mul, map_inv, hbt, inv_mul_cancel])
      have : t = b * (b⁻¹ * t) := by group
      rw [this]
      exact T.mul_mem (Subgroup.mem_sup_right hb) (Subgroup.mem_sup_left h1)
  have hm₀N : m₀ ∈ Subgroup.normalizer (T : Set ↥X) := by
    rw [Subgroup.mem_normalizer_iff]
    intro t
    rw [hTmem, hTmem, map_mul, map_mul, map_inv, hm₀]
    exact Subgroup.mem_normalizer_iff.1 hn (π t)
  obtain ⟨k, hkT, hkn⟩ := Sec15Frattini.exists_mem_normalizer_of_isSylowOf hEXsyl hm₀N
  have hπk : π k ∈ Eb := (hTmem k).1 hkT
  refine ⟨k⁻¹ * m₀, mem_normalizer_of_subgroupOf' hEX hkn, ?_⟩
  intro e he
  have heb : π e ∈ Eb := ⟨e, he, rfl⟩
  have hne : n * π e * n⁻¹ ∈ Eb := (Subgroup.mem_normalizer_iff.1 hn (π e)).1 heb
  have hcomm : ∀ a ∈ Eb, ∀ b ∈ Eb, a * b = b * a := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hEc _ (Subgroup.mem_subgroupOf.1 ha) _ (Subgroup.mem_subgroupOf.1 hb))
  have h1 : π (k⁻¹ * m₀ * e * (k⁻¹ * m₀)⁻¹) = (π k)⁻¹ * (n * π e * n⁻¹) * π k := by
    simp only [mul_inv_rev, map_mul, map_inv, hm₀, mul_assoc, inv_inv]
  rw [h1]
  have h2 := hcomm _ hne _ hπk
  calc (π k)⁻¹ * (n * π e * n⁻¹) * π k = (π k)⁻¹ * (π k * (n * π e * n⁻¹)) := by rw [← h2]; group
    _ = n * π e * n⁻¹ := by group


theorem exists_weyl_elem_of_conj {p : ℕ} (hp : p.Prime) {X E : Subgroup G} (θ : Subgroup ↥X)
    [θ.Normal] (hEX : E ≤ X) (hEel : IsElementaryAbelian p ↥E) (hθ : ¬ p ∣ Nat.card ↥θ)
    {R : Subgroup (↥X ⧸ θ)} {g : ↥X ⧸ θ}
    (hgR : conjSub g R = (E.subgroupOf X).map (QuotientGroup.mk' θ))
    {n : ↥X ⧸ θ} (hn : n ∈ Subgroup.normalizer (R : Set (↥X ⧸ θ))) {N : ℕ}
    (hnN : n ^ N ∈ Subgroup.center (↥X ⧸ θ)) {b : ↥X ⧸ θ} (hbR : b ∈ R)
    (hb : n * b * n⁻¹ ≠ b) :
    ∃ (m : ↥X) (hm : (m : G) ∈ Subgroup.normalizer (E : Set G)),
      conjAut E (m : G) hm ^ N = 1 ∧ conjAut E (m : G) hm ≠ 1 := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  set π := QuotientGroup.mk' θ with hπ
  set EX : Subgroup ↥X := E.subgroupOf X with hEXdef
  have hEp : IsPGroup p ↥E := hEel.isPGroup p ↥E
  have hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hEel.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hEXp : IsPGroup p ↥EX := hEp.of_equiv (Subgroup.subgroupOfEquivOfLe hEX).symm
  set n' : ↥X ⧸ θ := g * n * g⁻¹ with hn'def
  have hn' : n' ∈ Subgroup.normalizer ((EX.map π : Subgroup (↥X ⧸ θ)) : Set (↥X ⧸ θ)) := by
    rw [← hgR, Subgroup.mem_normalizer_iff]
    intro y
    rw [mem_conjSub_iff, mem_conjSub_iff]
    have h1 := Subgroup.mem_normalizer_iff.1 hn (g⁻¹ * y * g)
    have e : g⁻¹ * (n' * y * n'⁻¹) * g = n * (g⁻¹ * y * g) * n⁻¹ := by
      rw [hn'def]; group
    rw [e]
    exact h1
  obtain ⟨m, hmN, hact⟩ := exists_normalizer_lift hp θ hEX hEp hEc hθ hn'
  have hmX : ∀ f ∈ EX, m * f * m⁻¹ ∈ EX := by
    intro f hf
    have h1 := (Subgroup.mem_normalizer_iff.1 hmN (f : G)).1 (Subgroup.mem_subgroupOf.1 hf)
    exact Subgroup.mem_subgroupOf.2 (by simpa using h1)
  let ι : ↥E →* ↥X := Subgroup.inclusion hEX
  have hιmem : ∀ y : ↥E, ι y ∈ EX := fun y => Subgroup.mem_subgroupOf.2 (by simp [ι])
  set α : MulAut ↥E := conjAut E (m : G) hmN with hα
  have hαcoe : ∀ e : ↥E, ((α e : ↥E) : G) = (m : G) * (e : G) * (m : G)⁻¹ := fun e =>
    Equivariance.coe_conjAut hmN e
  have hαX : ∀ y : ↥E, ι (α y) = m * ι y * m⁻¹ := fun y =>
    Subtype.ext (by simp [ι, hαcoe])
  have hαpow : ∀ (j : ℕ) (e : ↥E), π (ι ((α ^ j) e)) = n' ^ j * π (ι e) * (n' ^ j)⁻¹ := by
    intro j
    induction j with
    | zero => intro e; simp
    | succ j ih =>
      intro e
      have h1 : ι ((α ^ (j + 1)) e) = m * ι ((α ^ j) e) * m⁻¹ := by
        rw [pow_succ', MulAut.mul_apply]
        exact hαX ((α ^ j) e)
      rw [h1, hact _ (hιmem _), ih, pow_succ']
      group
  refine ⟨m, hmN, ?_, ?_⟩
  · refine MulEquiv.ext fun e => ?_
    have h := hαpow N e
    have hn'N : n' ^ N = n ^ N := by
      rw [hn'def, conj_pow]
      have := Subgroup.mem_center_iff.1 hnN g
      calc g * n ^ N * g⁻¹ = n ^ N * g * g⁻¹ := by rw [this]
        _ = n ^ N := by group
    have hcen : n ^ N * π (ι e) * (n ^ N)⁻¹ = π (ι e) := by
      have := Subgroup.mem_center_iff.1 hnN (π (ι e))
      calc n ^ N * π (ι e) * (n ^ N)⁻¹ = π (ι e) * n ^ N * (n ^ N)⁻¹ := by rw [this]
        _ = π (ι e) := by group
    rw [hn'N, hcen] at h
    have h2 := Sec1511.eq_of_mk'_eq hEXp hθ (hιmem _) (hιmem e) h
    rw [MulAut.one_apply]
    refine Subtype.ext ?_
    have := congrArg (fun z : ↥X => (z : G)) h2
    simpa [ι] using this
  · intro h1'
    have h1 : α = 1 := h1'
    have hb' : g * b * g⁻¹ ∈ EX.map π := by
      rw [← hgR, mem_conjSub_iff]
      have e : g⁻¹ * (g * b * g⁻¹) * g = b := by group
      rw [e]
      exact hbR
    obtain ⟨e₀, he₀, hπe₀⟩ := hb'
    have he₀' : (e₀ : G) ∈ E := Subgroup.mem_subgroupOf.1 he₀
    have hιe : ι (⟨(e₀ : G), he₀'⟩ : ↥E) = e₀ := Subtype.ext rfl
    have h2 := hαpow 1 ⟨(e₀ : G), he₀'⟩
    rw [h1, pow_one, MulAut.one_apply, pow_one, hιe, hπe₀] at h2
    apply hb
    have h3 : g * b * g⁻¹ = g * (n * b * n⁻¹) * g⁻¹ := by
      rw [h2, hn'def]; group
    calc n * b * n⁻¹ = g⁻¹ * (g * (n * b * n⁻¹) * g⁻¹) * g := by group
      _ = g⁻¹ * (g * b * g⁻¹) * g := by rw [h3]
      _ = b := by group


theorem kf159ZFiveGen_of_weyl (h155 : Node155) (hMod : KFU5Mod) (hweyl : CenterWeylFive) :
    K1510R.KF159ZFiveGen := by
  classical
  intro G _ _ p A c L E h15 hF hout x hxE hx1 X hXx hpZ
  have h := h15.h12
  have hp := h.prime
  have : Fact p.Prime := ⟨hp⟩
  have hp5 : 5 ≤ p := by
    have h3 := h.three_lt
    by_contra hlt
    have h4 : p = 4 := by omega
    exact absurd (h4 ▸ hp) (by norm_num)
  have hEcard : Nat.card ↥E = p ^ 4 := by
    obtain ⟨-, -, -, -, -, hc, -⟩ := hout
    exact hc
  have hnonab : ∃ a b : G, a * b ≠ b * a := h.setup.2.1
  have hKP : IsKProper G := h.setup.2.2.1
  have hsimple : IsSimpleGroup G := h.setup.1
  have hrk3 : CFSG.twoLocalOddRank G ≤ 3 := h.setup.2.2.2.2.1.le
  have hEX : E ≤ Subgroup.normalizer (X : Set G) :=
    h.E_normalizes_thetaComponentsAt selected_prime_elements_normalize_theta_components hxE hXx
  have hXC : X ≤ Subgroup.centralizer ({x} : Set G) := (mem_thetaComponentsAt_iff.1 hXx).1
  have hXtop : X ≠ ⊤ := by
    intro htop
    exact EmbeddingFixedResidual.centralizer_ne_top_of_simple hnonab hx1
      (eq_top_iff.2 (htop ▸ hXC))
  have hKX : CFSG.IsKGroup ↥X := hKP X hXtop
  have hQq : CFSG.IsQuasisimple (↥X ⧸ aschbacherSolvableCore p ↥X) :=
    isQuasisimple_thetaQuotient_of_mem_thetaComponentsAt hp hXx
  have hZ2 : ¬ 2 ∣ Nat.card (Subgroup.center (↥X ⧸ aschbacherSolvableCore p ↥X)) :=
    N143.not_dvd_card_center_theta_quotient (L := ↥X) hp Nat.prime_two (by omega)
  have hodd : Odd (Nat.card (Subgroup.center (↥X ⧸ aschbacherSolvableCore p ↥X))) :=
    Nat.odd_iff.2 (by omega)
  have hrkX : CFSG.twoLocalOddRank ↥X ≤ 3 := by
    have h1 := Sec9A.evenRank_subgroup_le X
    rw [CFSG.RankThree.OddKernel.evenRank_eq_twoLocalOddRank,
      CFSG.RankThree.OddKernel.evenRank_eq_twoLocalOddRank] at h1
    exact h1.trans hrk3
  have hθp : ¬ p ∣ Nat.card ↥(aschbacherSolvableCore p ↥X) :=
    (solvable_prime_complement_core_characterization hp).2.2.1
  obtain ⟨P, hPsyl, hEP, hPW⟩ := exists_sylow_normalizer hp h155 X h15 hF hout
  obtain ⟨PW, hPWsyl, hPPW⟩ := Sec12Fus.exists_isSylowOf_ge (p := p) hPW hPsyl.2.1
  have hP' : CFSG.ABGLocalTools.IsSylowOf p P (X ⊔ E) := CFSG.ABGLocalTools.isSylowOf_iff.2 hPsyl
  have hPX : CFSG.ABGLocalTools.IsSylowOf p (P ⊓ X) X :=
    hP'.inf_of_le_normalizer le_sup_left (sup_le Subgroup.le_normalizer hEX)
  have key : ∀ R : Subgroup (↥X ⧸ aschbacherSolvableCore p ↥X), (∀ b ∈ R, b ^ p = 1) →
      (∀ a ∈ R, ∀ b ∈ R, a * b = b * a) → p ^ 4 ≤ Nat.card R →
      ∃ (g : ↥X ⧸ aschbacherSolvableCore p ↥X) (R' : Subgroup G), R' ≤ E ∧ R' ≤ P ⊓ X ∧
        Nat.card R' = Nat.card R ∧
        conjSub g R = (R'.subgroupOf X).map (QuotientGroup.mk' (aschbacherSolvableCore p ↥X)) := by
    intro R hRexp hRab hRcard
    obtain ⟨g, R', hR'P, hR'exp, hR'ab, hR'card, hgR⟩ :=
      exists_lift_elemAbelian_conj hp hPX hθp hRexp hRab
    refine ⟨g, R', ?_, hR'P, hR'card, hgR⟩
    refine le_E_of_elemAb hp h155 h15 hF hout hPWsyl
      (hR'P.trans inf_le_left |>.trans hPPW) hR'exp hR'ab ?_
    rw [hR'card]
    exact hRcard
  rcases hweyl ↥X hrkX hKX (aschbacherSolvableCore p ↥X) hQq p hp (by omega) hpZ hodd with
    ⟨R, hRexp, hRab, hRcard⟩ |
      ⟨hp5eq, R, hRexp, hRab, hRcard, ⟨n₃, hn₃N, hn₃c, b₃, hb₃R, hb₃⟩,
        ⟨n₅, hn₅N, hn₅c, b₅, hb₅R, hb₅⟩⟩
  ·
    obtain ⟨g, R', hR'E, -, hR'card, -⟩ := key R hRexp hRab
      (le_trans (Nat.pow_le_pow_right hp.pos (by norm_num)) hRcard)
    have h1 : Nat.card R' ≤ Nat.card E := Subgroup.card_le_of_le hR'E
    rw [hR'card, hEcard] at h1
    have h2 : p ^ 4 < p ^ 5 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
    omega
  ·
    subst hp5eq
    obtain ⟨g, R', hR'E, hR'PX, hR'card, hgR⟩ := key R hRexp hRab hRcard
    have hEeq : R' = E :=
      Subgroup.eq_of_le_of_card_ge hR'E (by rw [hR'card, hEcard]; exact hRcard)
    have hEX' : E ≤ X := by
      rw [← hEeq]
      exact hR'PX.trans inf_le_right
    rw [hEeq] at hgR
    have hEel : IsElementaryAbelian 5 ↥E := h.E_elem
    obtain ⟨M⟩ := Sec153.nonempty_modData hMod h15 hF hout
    obtain ⟨m₃, hm₃, hα₃pow, hα₃ne⟩ := exists_weyl_elem_of_conj hp
      (aschbacherSolvableCore 5 ↥X) hEX' hEel hθp hgR hn₃N hn₃c hb₃R hb₃
    obtain ⟨m₅, hm₅, hα₅pow, hα₅ne⟩ := exists_weyl_elem_of_conj hp
      (aschbacherSolvableCore 5 ↥X) hEX' hEel hθp hgR hn₅N hn₅c hb₅R hb₅
    have hfix : ∀ (m : ↥X) (hm : (m : G) ∈ Subgroup.normalizer (E : Set G)),
        conjAut E (m : G) hm ⟨x, hxE⟩ = ⟨x, hxE⟩ := by
      intro m hm
      refine Subtype.ext ?_
      rw [Equivariance.coe_conjAut hm]
      have := Subgroup.mem_centralizer_singleton_iff.1 (hXC m.2)
      calc (m : G) * x * (m : G)⁻¹ = x * (m : G) * (m : G)⁻¹ := by rw [this]
        _ = x := by group
    have hW : ∀ (m : ↥X) (hm : (m : G) ∈ Subgroup.normalizer (E : Set G)),
        conjAut E (m : G) hm ∈ torusWeyl E := fun m hm => ⟨⟨(m : G), hm⟩, rfl⟩
    have key2 := eq_one_of_fixed_order_three_five h M (hW m₃ hm₃) (hW m₅ hm₅) hα₃pow hα₃ne
      hα₅pow hα₅ne (hfix m₃ hm₃) (hfix m₅ hm₅)
    exact hx1 (congrArg Subtype.val key2)

end Lift

end CFSG.RankThree.PartOne.K159W
