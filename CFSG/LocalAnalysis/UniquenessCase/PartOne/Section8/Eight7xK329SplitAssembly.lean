module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight7xK329SplitDatum
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight7xK329SplitDefs
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight7xK329Layer
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight7xK329Reduce
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight7xK329SplitOrder

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open (StatedProj)

theorem k329_preimage_solvable {H : Type} [Group H] [Finite H] (Z : Subgroup H) [Z.Normal]
    (hZ : Z ≤ Subgroup.center H) (N : Subgroup (H ⧸ Z)) (hN : IsPGroup 3 N) :
    IsSolvable ↥(N.comap (QuotientGroup.mk' Z)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hnil : Group.IsNilpotent ↥N := hN.isNilpotent
  have hNs : Group.IsSolvable ↥N := inferInstance
  let Nt : Subgroup H := N.comap (QuotientGroup.mk' Z)
  have hZNt : Z ≤ Nt := by
    intro z hz
    have h1 : (QuotientGroup.mk' Z) z = 1 := (QuotientGroup.eq_one_iff z).2 hz
    show (QuotientGroup.mk' Z) z ∈ N
    rw [h1]
    exact N.one_mem
  let _ : CommGroup ↥Z := { (inferInstance : Group ↥Z) with
    mul_comm := fun a b => Subtype.ext (Subgroup.mem_center_iff.mp (hZ b.2) a) }
  let f : ↥Nt →* ↥N := (QuotientGroup.mk' Z).subgroupComap N
  refine Group.isSolvable_of_ker_le_range (Subgroup.inclusion hZNt) f ?_
  intro t ht
  have h1 : (QuotientGroup.mk (t : H) : H ⧸ Z) = 1 := congrArg Subtype.val ht
  have h2 : (t : H) ∈ Z := (QuotientGroup.eq_one_iff (t : H)).1 h1
  exact ⟨⟨t, h2⟩, rfl⟩

theorem k329_sylow_map_eq_top {A B : Type} [Group A] [Group B] [Finite A] {p : ℕ} [Fact p.Prime]
    (f : A →* B) (hf : Function.Surjective f) (hB : IsPGroup p B) (R : Sylow p A) :
    (R : Subgroup A).map f = ⊤ := by
  have h1 : ((R.mapSurjective hf : Sylow p B) : Subgroup B) = (R : Subgroup A).map f := rfl
  rw [← h1]
  exact ((R.mapSurjective hf).is_maximal' (hB.to_subgroup ⊤) le_top).symm

theorem k329_frame {H : Type} [Group H] (Z : Subgroup H) [Z.Normal] (hZ : Z ≤ Subgroup.center H)
    (x : H) :
    Subgroup.centralizer ({x} : Set H) ≤ K329Ct Z x ∧
      ((Subgroup.centralizer ({x} : Set H)).subgroupOf (K329Ct Z x)).Normal := by
  have hle : Subgroup.centralizer ({x} : Set H) ≤ K329Ct Z x := by
    intro c hc
    show (QuotientGroup.mk c : H ⧸ Z) ∈
      Subgroup.centralizer ({(QuotientGroup.mk x : H ⧸ Z)} : Set (H ⧸ Z))
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    have hxc : x * c = c * x := Subgroup.mem_centralizer_iff.1 hc x rfl
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hxc]
  refine ⟨hle, ?_⟩
  rw [Subgroup.normal_subgroupOf_iff hle]
  intro c g hc hg
  have hg' : (QuotientGroup.mk x : H ⧸ Z) * QuotientGroup.mk g =
      QuotientGroup.mk g * QuotientGroup.mk x := by
    have := hg
    simpa [K329Ct, Subgroup.mem_centralizer_iff] using this
  have hω : (g * x)⁻¹ * (x * g) ∈ Z := by
    rw [← QuotientGroup.eq, QuotientGroup.mk_mul, QuotientGroup.mk_mul]
    exact hg'.symm
  obtain ⟨ω, hωdef⟩ : ∃ ω, ω = (g * x)⁻¹ * (x * g) := ⟨_, rfl⟩
  rw [← hωdef] at hω
  have hωc : ∀ y : H, ω * y = y * ω := fun y => (Subgroup.mem_center_iff.mp (hZ hω) y).symm
  have hgxg : g⁻¹ * x * g = x * ω := by rw [hωdef]; group
  have hxc : x * c = c * x := Subgroup.mem_centralizer_iff.1 hc x rfl
  have key : (g⁻¹ * x * g) * c = c * (g⁻¹ * x * g) := by
    rw [hgxg]
    calc x * ω * c = x * (ω * c) := by rw [mul_assoc]
      _ = x * (c * ω) := by rw [hωc c]
      _ = (x * c) * ω := by rw [mul_assoc]
      _ = (c * x) * ω := by rw [hxc]
      _ = c * (x * ω) := by rw [mul_assoc]
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  rw [Set.mem_singleton_iff] at hh
  rw [hh]
  calc x * (g * c * g⁻¹) = g * ((g⁻¹ * x * g) * c) * g⁻¹ := by group
    _ = g * (c * (g⁻¹ * x * g)) * g⁻¹ := by rw [key]
    _ = (g * c * g⁻¹) * x := by group

theorem k329_layA {H : Type} [Group H] [Finite H] {C L : Subgroup H} (hcp : K329CentralProduct L)
    (hLC : L ≤ C) (hLn : (L.subgroupOf C).Normal) (N : Subgroup H) (hNC : N ≤ C)
    (hNn : (N.subgroupOf C).Normal) (hN : IsSolvable ↥N) : ⁅N, L⁆ = ⊥ := by
  obtain ⟨ι, hι, Lf, hq, hc, rfl⟩ := hcp
  have hLfC : ∀ i, Lf i ≤ C := fun i => (le_iSup Lf i).trans hLC
  have hsup : (⨆ i, Lf i).subgroupOf C = ⨆ i, (Lf i).subgroupOf C := by
    apply Subgroup.map_injective C.subtype_injective
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hLC, Subgroup.map_iSup]
    exact (iSup_congr fun i => by
      rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.2 (hLfC i)]).symm
  have hq' : ∀ i, CFSG.Open.IsQuasisimple ↥((Lf i).subgroupOf C) := fun i =>
    k329_isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe (hLfC i)).symm (hq i)
  have hc' : ∀ i j, i ≠ j → ⁅(Lf i).subgroupOf C, (Lf j).subgroupOf C⁆ = ⊥ := by
    intro i j hij
    apply Subgroup.map_injective C.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype,
      inf_eq_left.2 (hLfC i), inf_eq_left.2 (hLfC j), hc i j hij, Subgroup.map_bot]
  have hLn' : (⨆ i, (Lf i).subgroupOf C).Normal := hsup ▸ hLn
  have hNs : Group.IsSolvable ↥(N.subgroupOf C) := by
    have : Group.IsSolvable ↥N := hN
    exact Group.isSolvable_of_isSolvable_injective
      (f := ((Subgroup.subgroupOfEquivOfLe hNC) : ↥(N.subgroupOf C) →* ↥N))
      (Subgroup.subgroupOfEquivOfLe hNC).injective
  have : (N.subgroupOf C).Normal := hNn
  have key := k329_solvable_normal_centralizes (fun i => (Lf i).subgroupOf C) hq' hc' hLn'
    (N.subgroupOf C) hNs
  rw [← hsup] at key
  have h2 := congrArg (Subgroup.map C.subtype) key
  rw [Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype,
    inf_eq_left.2 hNC, inf_eq_left.2 hLC, Subgroup.map_bot] at h2
  exact h2

theorem k329_S1_zlift {H : Type} [Group H] [Finite H] (Z : Subgroup H) [Z.Normal]
    (hZ : Z ≤ Subgroup.center H) {x : H}
    (hz : K329ZDatum (H ⧸ Z) (QuotientGroup.mk x)) :
    ∃ Q : Subgroup H, Q ≤ K329Lres x ∧ (Q.subgroupOf (K329Lres x)).Normal ∧
      CFSG.Open.IsQuasisimple ↥Q ∧ Nat.card (↥Q ⧸ Subgroup.center ↥Q) = 504 := by
  obtain ⟨-, Y, hY, hYres, hYn⟩ := k329_S1_zResidual hz
  obtain ⟨h1, -, h3⟩ := k329_commutator_reduction Z hZ x
  have hres : K329Res (Subgroup.centralizer ({(QuotientGroup.mk x : H ⧸ Z)} : Set (H ⧸ Z))) =
      (K329Lres x).map (QuotientGroup.mk' Z) := by
    rw [k329_res_eq_of_commutator_le h1 h3, K329Lres, k329_res_map]
  rw [hres] at hYres hYn
  have hcard : Nat.card ↥Y = 504 := k329_card_psl28 hY
  have hsimple : IsSimpleGroup ↥Y :=
    CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags
      (by simp [CFSG.Blueprint.classicalTags]) hY
  have hna : ∃ a ∈ Y, ∃ b ∈ Y, a * b ≠ b * a := by
    by_contra hcon
    push Not at hcon
    let _ : CommGroup ↥Y := { (inferInstance : Group ↥Y) with
      mul_comm := fun a b => Subtype.ext (hcon a a.2 b b.2) }
    have hp := IsSimpleGroup.prime_card (α := ↥Y)
    rw [hcard] at hp
    norm_num at hp
  obtain ⟨Q, hQL, hQn, hQq, hQc⟩ := k329_res_lift Z hZ (K329Lres x) Y hYres hYn hsimple hna
  exact ⟨Q, hQL, hQn, hQq, hQc.trans hcard⟩

theorem k329_S1_twist {H : Type} [Group H] [Finite H] (Z : Subgroup H) [Z.Normal]
    (hZ : Z ≤ Subgroup.center H) {x : H}
    (hu : K329UDatum (H ⧸ Z) (QuotientGroup.mk x))
    (hcp : K329CentralProduct (K329Lres x)) (hs : K329Schur x) :
    ∃ g ∈ K329Ct Z x, g ∉ Subgroup.centralizer ({x} : Set H) ∧
      ∀ l ∈ K329Lres x, g * l = l * g := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨-, N, hNC, hNn, hN3, a, ha, b, hb, hab⟩ := k329_S1_uNormal hu
  obtain ⟨hCxCt, hCxn⟩ := k329_frame Z hZ x
  have hLCx : K329Lres x ≤ Subgroup.centralizer ({x} : Set H) := by
    intro l hl
    obtain ⟨c, -, rfl⟩ := Subgroup.mem_map.1 hl
    exact c.2
  have hLn : ((K329Lres x).subgroupOf (K329Ct Z x)).Normal := k329_res_normal hCxCt hCxn
  set Nt : Subgroup H := N.comap (QuotientGroup.mk' Z) with hNt
  have hNtC : Nt ≤ K329Ct Z x := Subgroup.comap_mono hNC
  have hNtn : (Nt.subgroupOf (K329Ct Z x)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hNtC]
    intro n g hn hg
    have hn' : (QuotientGroup.mk n : H ⧸ Z) ∈ N := hn
    have hg' : (QuotientGroup.mk g : H ⧸ Z) ∈
        Subgroup.centralizer ({QuotientGroup.mk x} : Set (H ⧸ Z)) := hg
    have h := (Subgroup.normal_subgroupOf_iff hNC).1 hNn (QuotientGroup.mk n) (QuotientGroup.mk g)
      hn' hg'
    show (QuotientGroup.mk (g * n * g⁻¹) : H ⧸ Z) ∈ N
    simpa using h
  have hNtsolv : IsSolvable ↥Nt := k329_preimage_solvable Z hZ N hN3
  have hcomm : ⁅Nt, K329Lres x⁆ = ⊥ :=
    k329_layA hcp (hLCx.trans hCxCt) hLn Nt hNtC hNtn hNtsolv
  by_contra hcon
  have hNtCx : Nt ≤ Subgroup.centralizer ({x} : Set H) := by
    intro g hg
    by_contra hgx
    refine hcon ⟨g, hNtC hg, hgx, fun l hl => ?_⟩
    have h1 := Subgroup.commutator_eq_bot_iff_le_centralizer.1 hcomm hg
    exact (Subgroup.mem_centralizer_iff.1 h1 l hl).symm
  obtain ⟨R⟩ : Nonempty (Sylow 3 ↥Nt) := inferInstance
  let f : ↥Nt →* ↥N := (QuotientGroup.mk' Z).subgroupComap N
  have hf : Function.Surjective f := by
    intro n
    obtain ⟨h, hh⟩ := QuotientGroup.mk_surjective (n : H ⧸ Z)
    exact ⟨⟨h, by show (QuotientGroup.mk h : H ⧸ Z) ∈ N; rw [hh]; exact n.2⟩, Subtype.ext hh⟩
  have hRtop : (R : Subgroup ↥Nt).map f = ⊤ := k329_sylow_map_eq_top f hf hN3 R
  set R' : Subgroup H := (R : Subgroup ↥Nt).map Nt.subtype with hR'
  have hR'Nt : R' ≤ Nt := by
    rintro _ ⟨r, -, rfl⟩
    exact r.2
  have hR'p : IsPGroup 3 R' := R.isPGroup'.map Nt.subtype
  have hR'comm : ⁅R', K329Lres x⁆ = ⊥ :=
    eq_bot_iff.2 ((Subgroup.commutator_mono hR'Nt le_rfl).trans hcomm.le)
  have hab' := hs R' (hR'Nt.trans hNtCx) hR'p hR'comm
  obtain ⟨r, hr, hra⟩ : ∃ r ∈ (R : Subgroup ↥Nt), f r = ⟨a, ha⟩ := by
    have h : (⟨a, ha⟩ : ↥N) ∈ (R : Subgroup ↥Nt).map f := by
      rw [hRtop]
      exact Subgroup.mem_top _
    exact Subgroup.mem_map.1 h
  obtain ⟨s, hs', hsb⟩ : ∃ s ∈ (R : Subgroup ↥Nt), f s = ⟨b, hb⟩ := by
    have h : (⟨b, hb⟩ : ↥N) ∈ (R : Subgroup ↥Nt).map f := by
      rw [hRtop]
      exact Subgroup.mem_top _
    exact Subgroup.mem_map.1 h
  have hrR : (r : H) ∈ R' := Subgroup.mem_map.2 ⟨r, hr, rfl⟩
  have hsR : (s : H) ∈ R' := Subgroup.mem_map.2 ⟨s, hs', rfl⟩
  have hcomm2 := hab' _ hrR _ hsR
  apply hab
  have e1 : (QuotientGroup.mk (r : H) : H ⧸ Z) = a := congrArg Subtype.val hra
  have e2 : (QuotientGroup.mk (s : H) : H ⧸ Z) = b := congrArg Subtype.val hsb
  rw [← e1, ← e2, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hcomm2]

theorem k329_Y_of_matrix {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K] [Finite K]
    (H : Subgroup (GL ι K)) (q : ℕ) (hM : K329YMatrix H q) {S : Type} [Group S]
    (e : S ≃* StatedProj H) {z : S} (hz : K329ZDatum S z) : q = 8 := by
  have hz' := K329ZDatum.of_mulEquiv e hz
  obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (e z)
  rw [← hx] at hz'
  have h3 : orderOf (QuotientGroup.mk x : H ⧸ K329Zh H) = 3 := hz'.1
  have hxZ : x ∉ K329Zh H := by
    intro hmem
    have h1 : (QuotientGroup.mk x : H ⧸ K329Zh H) = 1 := (QuotientGroup.eq_one_iff x).2 hmem
    rw [h1, orderOf_one] at h3
    exact absurd h3 (by norm_num)
  have hx3 : x ^ 3 ∈ K329Zh H := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, ← h3]
    exact pow_orderOf_eq_one _
  obtain ⟨Q, hQ⟩ := k329_S1_zlift (K329Zh H) (k329_Zh_le_center H) hz'
  exact hM x hxZ hx3 ⟨Q, hQ⟩

theorem k329_O3_of_matrix {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K] [Finite K]
    (H : Subgroup (GL ι K)) (concl : Prop) (hcp : K329CentralProductMatrix H)
    (hs : K329SchurMatrix H) (ht : K329TwistMatrix H concl) {S : Type} [Group S]
    (e : S ≃* StatedProj H) {u : S} (hu : K329UDatum S u) : concl := by
  have hu' := K329UDatum.of_mulEquiv e hu
  obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (e u)
  rw [← hx] at hu'
  have h3 : orderOf (QuotientGroup.mk x : H ⧸ K329Zh H) = 3 := hu'.1
  have hxZ : x ∉ K329Zh H := by
    intro hmem
    have h1 : (QuotientGroup.mk x : H ⧸ K329Zh H) = 1 := (QuotientGroup.eq_one_iff x).2 hmem
    rw [h1, orderOf_one] at h3
    exact absurd h3 (by norm_num)
  have hx3 : x ^ 3 ∈ K329Zh H := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, ← h3]
    exact pow_orderOf_eq_one _
  obtain ⟨g, hg, hgx, hgL⟩ :=
    k329_S1_twist (K329Zh H) (k329_Zh_le_center H) hu' (hcp x hxZ hx3) (hs x hxZ hx3)
  exact ht x hxZ hx3 g hg hgL hgx

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
