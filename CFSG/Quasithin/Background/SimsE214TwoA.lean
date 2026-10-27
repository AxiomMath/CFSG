module

public import CFSG.Quasithin.Vol2.E2FourteenA
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.Quasithin.SimsE2

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

namespace E214T

open scoped commutatorElement

theorem mem_center_of_sq_eq_one {X : Type} [Group X] [Finite X] {k : ℕ} (hk : 2 ≤ k)
    (hX : IsPSL 2 2 k X ∨ IsSz k X) {S : Subgroup X} (hS : IsSylowTwoOf S ⊤) {s : X}
    (hs : s ∈ S) (hs2 : s ^ 2 = 1) : s ∈ S ⊓ Subgroup.centralizer (S : Set X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_cases hs1 : s = 1
  · rw [hs1]
    exact Subgroup.one_mem _
  obtain ⟨j, hB⟩ := E2.exists_fusionBenderBorel_of_psl_or_sz hk hX
  have hB' : fusionBenderBorel ↥(⊤ : Subgroup X) (2 ^ k) j :=
    hB.map_mulEquiv Subgroup.topEquiv.symm
  obtain ⟨hcard, hsq⟩ := E2.card_inf_centralizer_of_fusionBenderBorel hB' hS
  have hidx : ¬ 2 ∣ S.index := by
    have := hS.2.2
    rwa [show (S.subgroupOf ⊤).index = S.index from Subgroup.relIndex_top_right S] at this
  have hSE := (hB (hS.2.1.toSylow hidx)).1
  have hM := CFSG.ComponentClassification.AschbacherToolkit.Bender.isStronglyEmbedded_of_fusion
    hSE
  obtain ⟨z, hz, hz1⟩ : ∃ z ∈ S ⊓ Subgroup.centralizer (S : Set X), z ≠ 1 := by
    by_contra hno
    push Not at hno
    have h1 : S ⊓ Subgroup.centralizer (S : Set X) = ⊥ :=
      (Subgroup.eq_bot_iff_forall _).2 hno
    rw [h1, Subgroup.card_bot] at hcard
    have : 2 ^ 1 < 2 ^ k := Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega
  have hSN : S ≤ Subgroup.normalizer
      (((hS.2.1.toSylow hidx : Sylow 2 X) : Subgroup X) : Set X) := by
    rw [IsPGroup.toSylow_coe]
    exact Subgroup.le_normalizer
  obtain ⟨n, hn, hnz⟩ := hM.involutions_conjugate_in (hSN hs) ⟨hs1, hs2⟩ (hSN hz.1)
    ⟨hz1, hsq z hz⟩
  rw [IsPGroup.toSylow_coe] at hn
  have hnz' : n⁻¹ * s * n = z := hnz
  have hsn : s = n * z * n⁻¹ := by rw [← hnz']; group
  rw [hsn]
  refine ⟨(Subgroup.mem_normalizer_iff.mp hn z).mp hz.1, Subgroup.mem_centralizer_iff.mpr
    fun y hy => ?_⟩
  have hy' : n⁻¹ * y * n ∈ S := by
    have := (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer (S : Set X)).inv_mem hn) y).mp
      hy
    simpa using this
  have hc := Subgroup.mem_centralizer_iff.mp hz.2 _ hy'
  calc y * (n * z * n⁻¹) = n * ((n⁻¹ * y * n) * z) * n⁻¹ := by group
    _ = n * (z * (n⁻¹ * y * n)) * n⁻¹ := by rw [hc]
    _ = n * z * n⁻¹ * y := by group

variable {G : Type} [Group G] [Finite G]

theorem star_eq_and_comm {T M V I : Subgroup G} {g : G} (hp : E2.Pair I (T ⊓ I) (M ⊓ I) V g)
    (hsyl : IsSylowTwoOf (T ⊓ I) I) (hTMI : T ⊓ I ≤ M ⊓ I) (hg : g ∈ I)
    (hgen : I = V ⊔ B6.conjSub g V)
    (hVZ : E2.star (M ⊓ I) I V ≤
      Subgroup.centralizer (E2.star (M ⊓ I) I (T ⊓ I) : Set (E2.StarQuot (M ⊓ I) I)))
    (hMN : M ⊓ I ≤ Subgroup.normalizer (V : Set G))
    (hBorel : E2.IsBorelIn ⊤ (E2.star (M ⊓ I) I (M ⊓ I))) {k : ℕ} (hk : 2 ≤ k)
    (hY : IsPSL 2 2 k (E2.StarQuot (M ⊓ I) I) ∨ IsSz k (E2.StarQuot (M ⊓ I) I)) :
    E2.star (M ⊓ I) I V = centerOf (E2.star (M ⊓ I) I (T ⊓ I)) ∧
      ∀ v ∈ V, v ∉ kerIn (M ⊓ I) I → ∃ u ∈ V, ∃ n ∈ M ⊓ I,
        (u * v)⁻¹ * (n⁻¹ * u * n) ∈ kerIn (M ⊓ I) I := by
  have := E2P.finite_starQuot (M ⊓ I) I
  have hS := E2.isSylowTwoOf_star_inf (M := M) hsyl
  obtain ⟨hcard, htrans⟩ := E2.exists_conj_of_mem_center hk hY hS
  have hBor := E2.star_eq_normalizer_of_isBorelIn hTMI hsyl hBorel
  have hN : E2.star (M ⊓ I) I (M ⊓ I) ≤
      Subgroup.normalizer (E2.star (M ⊓ I) I V : Set (E2.StarQuot (M ⊓ I) I)) :=
    E2.star_le_normalizer_star (inf_le_left.trans hMN)
  have hs : IsSimpleGroup (E2.StarQuot (M ⊓ I) I) := E2.isSimpleGroup_of_psl_or_sz hY
  have hV1 : E2.star (M ⊓ I) I V ≠ ⊥ := E2.star_ne_bot_of_gen hg hgen
  have hVT : E2.star (M ⊓ I) I V ≤ E2.star (M ⊓ I) I (T ⊓ I) :=
    Subgroup.map_mono (Subgroup.subgroupOf_mono I hp.le_T)
  have hle : E2.star (M ⊓ I) I V ≤ centerOf (E2.star (M ⊓ I) I (T ⊓ I)) := le_inf hVT hVZ
  have hVeq : E2.star (M ⊓ I) I V = centerOf (E2.star (M ⊓ I) I (T ⊓ I)) := by
    refine le_antisymm hle fun z hz => ?_
    by_cases hz1 : z = 1
    · rw [hz1]
      exact Subgroup.one_mem _
    obtain ⟨v, hv, hv1⟩ : ∃ v ∈ E2.star (M ⊓ I) I V, v ≠ 1 := by
      by_contra hcon
      push Not at hcon
      exact hV1 (eq_bot_iff.mpr fun x hx => (Subgroup.mem_bot).mpr (hcon x hx))
    obtain ⟨n, hn, hnz⟩ := htrans v (hle hv) z hz hv1 hz1
    have hnM : n ∈ E2.star (M ⊓ I) I (M ⊓ I) := by
      rw [hBor]
      exact hn
    have h2 := (Subgroup.mem_normalizer_iff.mp
      (hN ((E2.star (M ⊓ I) I (M ⊓ I)).inv_mem hnM)) v).mp hv
    rw [inv_inv, hnz] at h2
    exact h2
  refine ⟨hVeq, fun v hv hvJ => ?_⟩
  have hcard' : Nat.card ↥(centerOf (E2.star (M ⊓ I) I (T ⊓ I))) = 2 ^ k := hcard
  have hc4 : 2 < Nat.card ↥(E2.star (M ⊓ I) I V) := by
    rw [hVeq, hcard']
    calc 2 < 2 ^ 2 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  have hvI : v ∈ I := hp.V_le hv
  set sq := QuotientGroup.mk' ((kerIn (M ⊓ I) I).subgroupOf I) with hsq
  have hvs : sq ⟨v, hvI⟩ ∈ E2.star (M ⊓ I) I V := ⟨⟨v, hvI⟩, Subgroup.mem_subgroupOf.2 hv, rfl⟩
  have hv1 : sq ⟨v, hvI⟩ ≠ 1 := by
    rw [hsq, QuotientGroup.mk'_apply, Ne, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    exact hvJ
  obtain ⟨w, hw, hw1, hwv⟩ := E2.exists_mem_ne_of_two_lt_card hc4 (sq ⟨v, hvI⟩)
  obtain ⟨⟨u, huI⟩, hu, rfl⟩ := hw
  replace hu : u ∈ V := hu
  have hus : sq ⟨u, huI⟩ ∈ E2.star (M ⊓ I) I V := ⟨⟨u, huI⟩, Subgroup.mem_subgroupOf.2 hu, rfl⟩
  have huv : sq ⟨u, huI⟩ * sq ⟨v, hvI⟩ ∈ E2.star (M ⊓ I) I V := Subgroup.mul_mem _ hus hvs
  have huv1 : sq ⟨u, huI⟩ * sq ⟨v, hvI⟩ ≠ 1 := by
    intro h1
    apply hwv
    have hv2 := E2.sq_eq_one_of_mem_star hp.elem hvs
    calc sq ⟨u, huI⟩ = sq ⟨u, huI⟩ * (sq ⟨v, hvI⟩ * sq ⟨v, hvI⟩) := by rw [hv2, mul_one]
      _ = (sq ⟨u, huI⟩ * sq ⟨v, hvI⟩) * sq ⟨v, hvI⟩ := by group
      _ = sq ⟨v, hvI⟩ := by rw [h1, one_mul]
  obtain ⟨n, hn, hnz⟩ := htrans _ (hle hus) _ (hle huv) hw1 huv1
  have hnM : n ∈ E2.star (M ⊓ I) I (M ⊓ I) := by
    rw [hBor]
    exact hn
  obtain ⟨⟨n₀, hn₀I⟩, hn₀, rfl⟩ := hnM
  replace hn₀ : n₀ ∈ M ⊓ I := hn₀
  refine ⟨u, hu, n₀, hn₀, ?_⟩
  have hnz' : sq ((⟨n₀, hn₀I⟩ : I)⁻¹ * ⟨u, huI⟩ * ⟨n₀, hn₀I⟩) = sq (⟨u, huI⟩ * ⟨v, hvI⟩) := by
    rw [map_mul, map_mul, map_mul, map_inv]
    exact hnz
  rw [hsq, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
    Subgroup.mem_subgroupOf] at hnz'
  have e : ((((⟨n₀, hn₀I⟩ : I)⁻¹ * ⟨u, huI⟩ * ⟨n₀, hn₀I⟩)⁻¹ * (⟨u, huI⟩ * ⟨v, hvI⟩) : I) : G) =
      ((u * v)⁻¹ * (n₀⁻¹ * u * n₀))⁻¹ := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  rw [e] at hnz'
  have h3 := (kerIn (M ⊓ I) I).inv_mem hnz'
  rw [inv_inv] at h3
  exact h3

theorem mem_kerIn_iff {T M V I : Subgroup G} {g : G} (hp : E2.Pair I (T ⊓ I) (M ⊓ I) V g)
    [((E2.Pair.PP (M ⊓ I) V I g).subgroupOf I).Normal]
    (hZJ : Subgroup.center (E2.Pair.Xbar (M ⊓ I) V I g) = E2.Pair.Jbar (M ⊓ I) V I g) (x : G) :
    x ∈ kerIn (M ⊓ I) I ↔
      x ∈ I ∧ ∀ y ∈ I, x * y * x⁻¹ * y⁻¹ ∈ E2.Pair.PP (M ⊓ I) V I g := by
  constructor
  · intro hx
    refine ⟨kerIn_le.trans hp.le_X hx, fun y hy => ?_⟩
    have h1 := hp.commutator_kerIn_mem_P hy hx
    have e : x * y * x⁻¹ * y⁻¹ = (y * x * y⁻¹ * x⁻¹)⁻¹ := by group
    rw [e]
    exact Subgroup.inv_mem _ h1
  · rintro ⟨hxI, hxc⟩
    set q := QuotientGroup.mk' ((E2.Pair.PP (M ⊓ I) V I g).subgroupOf I) with hq
    have hcen : q ⟨x, hxI⟩ ∈ Subgroup.center (E2.Pair.Xbar (M ⊓ I) V I g) := by
      rw [Subgroup.mem_center_iff]
      intro w
      obtain ⟨⟨y, hyI⟩, rfl⟩ := QuotientGroup.mk'_surjective _ w
      rw [← map_mul, ← map_mul, hq, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
        QuotientGroup.eq, Subgroup.mem_subgroupOf]
      have h1 := hxc y hyI
      have h2 : (y * x)⁻¹ * (x * y * x⁻¹ * y⁻¹) * (y * x)⁻¹⁻¹ ∈ E2.Pair.PP (M ⊓ I) V I g :=
        (Subgroup.mem_normalizer_iff.mp
          (hp.le_normalizer_P (I.inv_mem (I.mul_mem hyI hxI))) _).mp h1
      have e : (((⟨y, hyI⟩ * ⟨x, hxI⟩ : I)⁻¹ * (⟨x, hxI⟩ * ⟨y, hyI⟩ : I) : I) : G) =
          (y * x)⁻¹ * (x * y * x⁻¹ * y⁻¹) * (y * x)⁻¹⁻¹ := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        group
      rw [e]
      exact h2
    rw [hZJ] at hcen
    obtain ⟨⟨j, hjI⟩, hj, hjx⟩ := hcen
    replace hj : j ∈ kerIn (M ⊓ I) I := Subgroup.mem_subgroupOf.1 hj
    rw [hq, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
      Subgroup.mem_subgroupOf] at hjx
    have hjx' : j⁻¹ * x ∈ kerIn (M ⊓ I) I := hp.P_le_J hjx
    have e : x = j * (j⁻¹ * x) := by group
    rw [e]
    exact Subgroup.mul_mem _ hj hjx'

theorem two_of_psl_sz
    (hKG1 : E2.KGSz8CoverInvolutions) (hKG3 : E2.KGI22One)
    {T M V I : Subgroup G} {g : G} (hp : E2.Pair I (T ⊓ I) (M ⊓ I) V g)
    (hsyl : IsSylowTwoOf (T ⊓ I) I) (hTMI : T ⊓ I ≤ M ⊓ I) (hg : g ∈ I)
    (hgen : I = V ⊔ B6.conjSub g V)
    (hVZ : E2.star (M ⊓ I) I V ≤
      Subgroup.centralizer (E2.star (M ⊓ I) I (T ⊓ I) : Set (E2.StarQuot (M ⊓ I) I)))
    (hMN : M ⊓ I ≤ Subgroup.normalizer (V : Set G))
    (hBorel : E2.IsBorelIn ⊤ (E2.star (M ⊓ I) I (M ⊓ I))) {k : ℕ} (hk : 2 ≤ k)
    (hY : IsPSL 2 2 k (E2.StarQuot (M ⊓ I) I) ∨ IsSz k (E2.StarQuot (M ⊓ I) I)) :
    E2.star (M ⊓ I) I V = centerOf (E2.star (M ⊓ I) I (T ⊓ I)) ∧
      (E2.Pair.PP (M ⊓ I) V I g = kerIn (M ⊓ I) I ∨
        (∃ (_ : ((E2.Pair.PP (M ⊓ I) V I g).subgroupOf I).Normal),
          CFSG.IsQuasisimple (↥I ⧸ (E2.Pair.PP (M ⊓ I) V I g).subgroupOf I) ∧
          IsSz 3 (E2.StarQuot (M ⊓ I) I) ∧
          (∀ x : G, x ∈ kerIn (M ⊓ I) I ↔
            x ∈ I ∧ ∀ y ∈ I, x * y * x⁻¹ * y⁻¹ ∈ E2.Pair.PP (M ⊓ I) V I g) ∧
          V ⊔ E2.Pair.PP (M ⊓ I) V I g =
            ⁅Subgroup.closure {t : G | t ∈ T ⊓ I ∧ t ^ 2 ∈ E2.Pair.PP (M ⊓ I) V I g}, M ⊓ I⁆ ⊔
              E2.Pair.PP (M ⊓ I) V I g ∧
          E2.IsBorelIn ⊤ (E2.star (M ⊓ I) I (M ⊓ I)) ∧
          E2.star (M ⊓ I) I V = centerOf (E2.star (M ⊓ I) I (T ⊓ I)))) := by
  have := E2P.finite_starQuot (M ⊓ I) I
  obtain ⟨hVeq, hcomm⟩ := star_eq_and_comm hp hsyl hTMI hg hgen hVZ hMN hBorel hk hY
  refine ⟨hVeq, ?_⟩
  by_cases hPJ : E2.Pair.PP (M ⊓ I) V I g = kerIn (M ⊓ I) I
  · exact Or.inl hPJ
  right
  have := hp.normal_P
  have := hp.normal_Jbar
  set PP := E2.Pair.PP (M ⊓ I) V I g with hPP
  set J := kerIn (M ⊓ I) I with hJdef
  have hVbar : E2.Pair.Vbar (M ⊓ I) V I g ≤ commutator (E2.Pair.Xbar (M ⊓ I) V I g) :=
    hp.Vbar_le_commutator fun v hv hvJ => by
      obtain ⟨u, hu, n, hn, h⟩ := hcomm v hv hvJ
      exact ⟨u, hu, n, ⟨hn.2, hMN hn⟩, h⟩
  have htop : (⊤ : Subgroup (E2.Pair.Xbar (M ⊓ I) V I g)) =
      commutator (E2.Pair.Xbar (M ⊓ I) V I g) :=
    le_antisymm (hp.top_eq_commutator_sup_Vbar.le.trans (sup_le le_rfl hVbar)) le_top
  obtain ⟨hZJ, -, -⟩ := hp.center_seven hKG1 hKG3 (by omega : 1 < k) hY
  have hSz3 : IsSz 3 (E2.StarQuot (M ⊓ I) I) := by
    obtain ⟨hcase, -⟩ := hp.center_commutator_seven hKG1 hKG3 (by omega : 1 < k) hY
    rcases hcase with hZL | ⟨hSz3, -⟩
    swap
    · exact hSz3
    exfalso
    apply hPJ
    have hZX : Subgroup.center (E2.Pair.Xbar (M ⊓ I) V I g) = ⊥ := by
      refine eq_bot_iff.mpr fun z hz => ?_
      have hzc : z ∈ commutator (E2.Pair.Xbar (M ⊓ I) V I g) := htop ▸ Subgroup.mem_top z
      have hz' : (⟨z, hzc⟩ : commutator (E2.Pair.Xbar (M ⊓ I) V I g)) ∈
          Subgroup.center (commutator (E2.Pair.Xbar (M ⊓ I) V I g)) := by
        rw [Subgroup.mem_center_iff]
        intro w
        exact Subtype.ext ((Subgroup.mem_center_iff.mp hz) w)
      rw [hZL, Subgroup.mem_bot] at hz'
      exact (Subgroup.mem_bot).mpr (congrArg Subtype.val hz')
    rw [hZX] at hZJ
    refine le_antisymm hp.P_le_J fun j hj => ?_
    have hjI : j ∈ I := kerIn_le.trans hp.le_X hj
    have h1 : QuotientGroup.mk' (PP.subgroupOf I) (⟨j, hjI⟩ : I) ∈
        E2.Pair.Jbar (M ⊓ I) V I g := ⟨⟨j, hjI⟩, Subgroup.mem_subgroupOf.2 hj, rfl⟩
    rw [← hZJ, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
      Subgroup.mem_subgroupOf] at h1
    exact h1
  have hJiff := mem_kerIn_iff hp hZJ
  refine ⟨hp.normal_P, ?_, hSz3, hJiff, ?_, hBorel, hVeq⟩
  ·
    have hXs := E2.isSimpleGroup_of_psl_or_sz hY
    let e : E2.Pair.Xbar (M ⊓ I) V I g ⧸ Subgroup.center (E2.Pair.Xbar (M ⊓ I) V I g) ≃*
        E2.StarQuot (M ⊓ I) I :=
      (QuotientGroup.quotientMulEquivOfEq hZJ).trans hp.quotJbarEquiv
    refine ⟨⟨htop.symm⟩, e.isSimpleGroup, ?_⟩
    obtain ⟨a, b, hab⟩ := E2.nonabelian_of_psl_or_sz (by omega : 1 < k) hY
    exact ⟨e.symm a, e.symm b, fun hh => hab (by simpa using congrArg e hh)⟩
  ·
    set C := Subgroup.closure {t : G | t ∈ T ⊓ I ∧ t ^ 2 ∈ PP} with hC
    have hBP : J ⊓ V ≤ PP := le_sup_left
    have hVTI : V ≤ T ⊓ I := hp.le_T
    have hCVJ : C ≤ V ⊔ J := by
      rw [hC, Subgroup.closure_le]
      rintro t ⟨htTI, ht2⟩
      have hS := E2.isSylowTwoOf_star_inf (M := M) hsyl
      set sq := QuotientGroup.mk' (J.subgroupOf I) with hsq
      have htT : sq ⟨t, htTI.2⟩ ∈ E2.star (M ⊓ I) I (T ⊓ I) :=
        ⟨⟨t, htTI.2⟩, Subgroup.mem_subgroupOf.2 htTI, rfl⟩
      have ht2' : sq ⟨t, htTI.2⟩ ^ 2 = 1 := by
        rw [← map_pow, hsq, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
          Subgroup.mem_subgroupOf]
        exact hp.P_le_J ht2
      have hZ := mem_center_of_sq_eq_one hk hY hS htT ht2'
      have hZ' : sq ⟨t, htTI.2⟩ ∈ E2.star (M ⊓ I) I V := by
        rw [hVeq]
        exact hZ
      obtain ⟨⟨v, hvI⟩, hv, hvt⟩ := hZ'
      replace hv : v ∈ V := Subgroup.mem_subgroupOf.1 hv
      rw [hsq, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
        Subgroup.mem_subgroupOf] at hvt
      have hvt' : v⁻¹ * t ∈ J := by simpa using hvt
      have e : t = v * (v⁻¹ * t) := by group
      show t ∈ V ⊔ J
      rw [e]
      exact Subgroup.mul_mem_sup hv hvt'
    have hVJn : V ≤ Subgroup.normalizer (J : Set G) := hp.V_le.trans (le_normalizer_kerIn _ _)
    refine le_antisymm (sup_le ?_ le_sup_right) (sup_le ?_ le_sup_right)
    ·
      intro v hv
      by_cases hvJ : v ∈ J
      · exact Subgroup.mem_sup_right (hBP ⟨hvJ, hv⟩)
      obtain ⟨u, hu, n, hn, hw⟩ := hcomm v hv hvJ
      have hnu : n⁻¹ * u * n ∈ V := by
        have := (Subgroup.mem_normalizer_iff.mp
          ((Subgroup.normalizer (V : Set G)).inv_mem (hMN hn)) u).mp hu
        simpa using this
      have hwV : (u * v)⁻¹ * (n⁻¹ * u * n) ∈ V :=
        V.mul_mem (V.inv_mem (V.mul_mem hu hv)) hnu
      have huC : u⁻¹ ∈ C := Subgroup.subset_closure ⟨(T ⊓ I).inv_mem (hVTI hu), by
        rw [inv_pow, hp.elem.2 u hu, inv_one]
        exact Subgroup.one_mem _⟩
      have hcm : ⁅u⁻¹, n⁻¹⁆ ∈ ⁅C, M ⊓ I⁆ :=
        Subgroup.commutator_mem_commutator huC ((M ⊓ I).inv_mem hn)
      have e : v = ⁅u⁻¹, n⁻¹⁆ * ((u * v)⁻¹ * (n⁻¹ * u * n))⁻¹ := by
        rw [commutatorElement_def]
        group
      rw [e]
      exact Subgroup.mul_mem_sup hcm (PP.inv_mem (hBP ⟨hw, hwV⟩))
    ·
      rw [Subgroup.commutator_le]
      intro c hc m hm
      have hc' : c ∈ ((V ⊔ J : Subgroup G) : Set G) := hCVJ hc
      rw [Subgroup.coe_mul_of_left_le_normalizer_right V J hVJn] at hc'
      obtain ⟨v, hv, j, hj, rfl⟩ := hc'
      have hjm : j * m * j⁻¹ * m⁻¹ ∈ PP := ((hJiff j).1 hj).2 m hm.2
      have hmv : m * v⁻¹ * m⁻¹ ∈ V :=
        (Subgroup.mem_normalizer_iff.mp (hMN hm) v⁻¹).mp (V.inv_mem hv)
      have e : ⁅v * j, m⁆ = v * (j * m * j⁻¹ * m⁻¹) * (m * v⁻¹ * m⁻¹) := by
        rw [commutatorElement_def]
        group
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_left hv)
        (Subgroup.mem_sup_right hjm)) (Subgroup.mem_sup_left hmv)

end E214T

end CFSG.Quasithin.SimsE2
