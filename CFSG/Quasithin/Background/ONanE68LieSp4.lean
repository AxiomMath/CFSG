module

public import CFSG.Quasithin.Background.ONanE68LieRank1
public import CFSG.Quasithin.Background.ONanE68LieRank2
public import CFSG.Quasithin.Background.ONanE68LieSp4Alg

public section

namespace CFSG.Quasithin

namespace E6

namespace E68Proof

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.H13.KG68

section Lattice

variable {G : Type} [Group G]

theorem maximal_of_lattice {B P₁ P₂ L X : Subgroup G} (hsup : P₁ ⊔ P₂ = L)
    (honly : ∀ Y : Subgroup G, B < Y → Y < L → Y = P₁ ∨ Y = P₂) (hBX : B < X) (hXL : X < L) :
    ∀ K : Subgroup G, X ≤ K → K ≤ L → K = X ∨ K = L := by
  intro K hXK hKL
  by_cases hKX : K = X
  · exact Or.inl hKX
  right
  by_contra hKL'
  have hKlt : K < L := lt_of_le_of_ne hKL hKL'
  have hXK' : X < K := lt_of_le_of_ne hXK fun h => hKX h.symm
  rcases honly X hBX hXL with hX | hX <;> rcases honly K (hBX.trans hXK') hKlt with hK | hK
  · exact hXK'.ne (hX.trans hK.symm)
  · rw [hX, hK] at hXK'
    rw [sup_eq_right.2 hXK'.le] at hsup
    exact hKlt.ne (hK.trans hsup)
  · rw [hX, hK] at hXK'
    rw [sup_eq_left.2 hXK'.le] at hsup
    exact hKlt.ne (hK.trans hsup)
  · exact hXK'.ne (hX.trans hK.symm)

end Lattice

section Geometry

variable {G : Type} [Group G] [Finite G] {T M V U L : Subgroup G}

theorem decomp_of_theta_fixed (hV : CFSG.Open.IsElemAbelian 2 V) (h : HypE61 T M V)
    (hU : U ∈ gammaE64 V M) (hL : IsComponentIn L (Subgroup.centralizer (U : Set G)))
    (hZ2 : IsPGroup 2 (Subgroup.center ↥L)) (hBX : borOf T V L ≤ L ⊓ M)
    (θ : ↥V →* Bar.Qbar L)
    (hθ : ∀ a : ↥V, Bar.barHom L ⟨a, le_normalizer_of_component h hU hL a.2⟩ = MulAut.conj (θ a))
    (hfix : ∀ w ∈ θ.range,
      (∀ b ∈ Subgroup.normalizer (sylowBar T V L : Set (Bar.Qbar L)), b * w * b⁻¹ = w) → w = 1) :
    (V ⊓ Subgroup.centralizer (L : Set G)) ⊓ ⁅V, L ⊓ M⁆ = ⊥ ∧
      (V ⊓ Subgroup.centralizer (L : Set G)) ⊔ ⁅V, L ⊓ M⁆ = V := by
  have hZ := center_le_sylow h hU hL hZ2
  have hq : CFSG.IsQuasisimple ↥L := BenderBranch.isQuasisimple_of_isComponentIn hL
  have hZ0 := center_qbar_eq_bot hq
  have hperf : Group.IsPerfect ↥L := hq.1
  have hVN : V ≤ Subgroup.normalizer (L : Set G) := le_normalizer_of_component h hU hL
  obtain ⟨-, hres, hXN⟩ := sandwich h hU hL
  have hodd := odd_card_autI hV hXN (hres.trans inf_le_right)
  have hXU : L ⊓ M ≤ Subgroup.centralizer ((V ⊓ Subgroup.centralizer (L : Set G) : Subgroup G) :
      Set G) := inf_le_left.trans (le_centralizer_inf_centralizer V L)
  refine decomp_of_fixed hV inf_le_left hXN hXU hodd ?_
  intro v hv hfv
  refine ⟨hv, ?_⟩
  refine (theta_eq_one_iff hVN θ hθ hZ0 hperf ⟨v, hv⟩).1 (hfix _ ⟨⟨v, hv⟩, rfl⟩ ?_)
  intro b hb
  obtain ⟨y, hyB, rfl⟩ := exists_mem_borOf_of_mem_normalizer hZ hb
  have hyX : y ∈ L ⊓ M := hBX hyB
  have h1 := theta_comm_of_comm hVN θ hθ ⟨y, hyX.1⟩ ⟨v, hv⟩ (hfv y hyX)
  rw [piG_of_mem hyX.1, h1]
  group

theorem not_inf_le_borOf_of_Zx (h : HypE61 T M V) (hU : U ∈ gammaE64 V M)
    (hL : IsComponentIn L (Subgroup.centralizer (U : Set G))) (hZ0L : Subgroup.center ↥L = ⊥)
    (θ : ↥V →* Bar.Qbar L)
    (hθ : ∀ a : ↥V, Bar.barHom L ⟨a, le_normalizer_of_component h hU hL a.2⟩ = MulAut.conj (θ a))
    {Zx : Subgroup (Bar.Qbar L)} (hW : θ.range = Zx)
    (hcent : ¬ Subgroup.centralizer (Zx : Set (Bar.Qbar L)) ≤
      Subgroup.normalizer (sylowBar T V L : Set (Bar.Qbar L))) : ¬ L ⊓ M ≤ borOf T V L := by
  intro hXB
  have hZ := center_le_sylow h hU hL (isPGroup_two_of_center_eq_bot hZ0L)
  have hVN : V ≤ Subgroup.normalizer (L : Set G) := le_normalizer_of_component h hU hL
  have hinj : Function.Injective (piBar L) := by
    rw [← MonoidHom.ker_eq_bot_iff, ker_piBar, hZ0L]
  obtain ⟨hCX, -, -⟩ := sandwich h hU hL
  obtain ⟨y', hy'C, hy'N⟩ := IsConcreteLE.not_le_iff_exists.1 hcent
  obtain ⟨l, rfl⟩ := piBar_surjective (L := L) y'
  have hl : (l : G) ∈ L ⊓ Subgroup.centralizer (V : Set G) := by
    refine ⟨l.2, Subgroup.mem_centralizer_iff.2 fun a ha => ?_⟩
    have hmem : θ ⟨a, ha⟩ ∈ Zx := hW ▸ ⟨⟨a, ha⟩, rfl⟩
    have h1 := Subgroup.mem_centralizer_iff.1 hy'C _ hmem
    exact (comm_of_theta_comm hVN θ hθ hinj l ⟨a, ha⟩ h1.symm).symm
  exact hy'N ((mem_borOf_iff hZ).1 (hXB (hCX hl))).2

theorem case2b_of_Zx (hV : CFSG.Open.IsElemAbelian 2 V) (h : HypE61 T M V) (hU : U ∈ gammaE64 V M)
    (hL : IsComponentIn L (Subgroup.centralizer (U : Set G))) (hZ0L : Subgroup.center ↥L = ⊥)
    {n : ℕ} (hn : 2 ≤ n) (hBX : borOf T V L ≤ M) (θ : ↥V →* Bar.Qbar L)
    (hθ : ∀ a : ↥V, Bar.barHom L ⟨a, le_normalizer_of_component h hU hL a.2⟩ = MulAut.conj (θ a))
    {Zx : Subgroup (Bar.Qbar L)} {x : Bar.Qbar L} (hW : θ.range = Zx)
    (hxS : SingerHyp (Subgroup.normalizer (sylowBar T V L : Set (Bar.Qbar L))) Zx x)
    (hcard : Nat.card Zx = 2 ^ n)
    (hauto : ∀ y ∈ Subgroup.normalizer (Zx : Set (Bar.Qbar L)),
      ∃ b ∈ Subgroup.normalizer (sylowBar T V L : Set (Bar.Qbar L)),
        ∀ z ∈ Zx, y * z * y⁻¹ = b * z * b⁻¹)
    (hcent : ¬ Subgroup.centralizer (Zx : Set (Bar.Qbar L)) ≤
      Subgroup.normalizer (sylowBar T V L : Set (Bar.Qbar L)))
    {P₁ P₂ : Subgroup G} (hsup : P₁ ⊔ P₂ = L)
    (honly : ∀ Y : Subgroup G, borOf T V L < Y → Y < L → Y = P₁ ∨ Y = P₂) :
    borOf T V L ≤ L ⊓ M ∧ L ⊓ M < L ∧
      (∀ K : Subgroup G, L ⊓ M ≤ K → K ≤ L → K = L ⊓ M ∨ K = L) ∧
      E3.mQuot V (V ⊓ Subgroup.centralizer (L : Set G)) = n ∧
      (1 < n → IsCyclic (autI hV (L ⊓ M)) ∧ Nat.card (autI hV (L ⊓ M)) = 2 ^ n - 1) := by
  have hZ2 := isPGroup_two_of_center_eq_bot hZ0L
  have hZ := center_le_sylow h hU hL hZ2
  have hq : CFSG.IsQuasisimple ↥L := BenderBranch.isQuasisimple_of_isComponentIn hL
  have hZ0 := center_qbar_eq_bot hq
  have hperf : Group.IsPerfect ↥L := hq.1
  have hLM : ¬ L ≤ M := not_le_of_component h hU.1 hL
  have hVN : V ≤ Subgroup.normalizer (L : Set G) := le_normalizer_of_component h hU hL
  obtain ⟨-, hres, hXN⟩ := sandwich h hU hL
  have hBX' : borOf T V L ≤ L ⊓ M := le_inf borOf_le_left hBX
  have hXL : L ⊓ M < L := lt_of_le_of_ne inf_le_left fun hh => hLM (hh ▸ inf_le_right)
  have hnotB := not_inf_le_borOf_of_Zx h hU hL hZ0L θ hθ hW hcent
  have hBlt : borOf T V L < L ⊓ M := lt_of_le_of_ne hBX' fun hh => hnotB hh.ge
  have hm : E3.mQuot V (V ⊓ Subgroup.centralizer (L : Set G)) = n :=
    mQuot_eq_of_card_range h.isPGroup_V hVN θ hθ hZ0 hperf (by rw [hW]; exact hcard)
  refine ⟨hBX', hXL, maximal_of_lattice hsup honly hBlt hXL, hm, fun _ => ?_⟩
  have hodd := odd_card_autI hV hXN (hres.trans inf_le_right)
  have hBW : Subgroup.normalizer (sylowBar T V L : Set (Bar.Qbar L)) ≤
      Subgroup.normalizer (Zx : Set (Bar.Qbar L)) :=
    fun b hb => mem_normalizer_of_conj_le fun z hz => hxS.inv b hb z hz
  have hW0 : Zx ≠ ⊥ := by
    intro h0
    rw [h0, Subgroup.card_bot] at hcard
    have : 1 < 2 ^ n := Nat.one_lt_two_pow (by omega)
    omega
  obtain ⟨x₀, hx₀B, hx₀⟩ := exists_mem_borOf_of_mem_normalizer hZ hxS.mem
  have hXB' : ∀ y ∈ L ⊓ M, ∃ b ∈ Subgroup.normalizer (sylowBar T V L : Set (Bar.Qbar L)),
      ∀ w ∈ Zx, piG L y * w * (piG L y)⁻¹ = b * w * b⁻¹ := by
    intro y hy
    have hyN : piG L y ∈ Subgroup.normalizer (Zx : Set (Bar.Qbar L)) :=
      mem_normalizer_of_conj_le fun w hw => hW ▸ theta_range_invariant hVN θ hθ hZ0 hy.1
        (hXN hy) w (hW ▸ hw)
    exact hauto _ hyN
  obtain ⟨hcyc, hcard'⟩ := autI_cyclic_of_singerHyp hV hXN inf_le_left hodd hVN θ hθ hZ0 hperf
    hxS hBW hW hW0 (hBX' hx₀B) hx₀ hXB'
  exact ⟨hcyc, by rw [hcard', hcard]⟩

theorem exists_A_of_range_eq (h : HypE61 T M V) (hU : U ∈ gammaE64 V M)
    (hL : IsComponentIn L (Subgroup.centralizer (U : Set G))) (hZ0L : Subgroup.center ↥L = ⊥)
    {n : ℕ} (hn : 2 ≤ n) (θ : ↥V →* Bar.Qbar L)
    (hθ : ∀ a : ↥V, Bar.barHom L ⟨a, le_normalizer_of_component h hU hL a.2⟩ = MulAut.conj (θ a))
    {Zs Zl : Subgroup (Bar.Qbar L)} (hW : θ.range = omegaCenter (sylowBar T V L))
    (hZsZ : Zs ≤ omegaCenter (sylowBar T V L)) (hZlZ : Zl ≤ omegaCenter (sylowBar T V L))
    (hinf : Zs ⊓ Zl = ⊥) (hcs : Nat.card Zs = 2 ^ n) (hcl : Nat.card Zl = 2 ^ n)
    (hcZ : Nat.card (omegaCenter (sylowBar T V L)) = 2 ^ (2 * n))
    (hcent : ¬ Subgroup.centralizer (Zs : Set (Bar.Qbar L)) ≤
      Subgroup.normalizer (sylowBar T V L : Set (Bar.Qbar L)))
    (hXeq : L ⊓ M = borOf T V L) :
    ∃ A : Subgroup G, U < A ∧ A < V ∧ E3.mQuot V A = n ∧
      ¬ L ⊓ Subgroup.centralizer (A : Set G) ≤ M := by
  classical
  have hZ := center_le_sylow h hU hL (isPGroup_two_of_center_eq_bot hZ0L)
  have hq : CFSG.IsQuasisimple ↥L := BenderBranch.isQuasisimple_of_isComponentIn hL
  have hZ0 := center_qbar_eq_bot hq
  have hperf : Group.IsPerfect ↥L := hq.1
  have hVN : V ≤ Subgroup.normalizer (L : Set G) := le_normalizer_of_component h hU hL
  have hinj : Function.Injective (piBar L) := by
    rw [← MonoidHom.ker_eq_bot_iff, ker_piBar, hZ0L]
  set A : Subgroup G := (Zs.comap θ).map V.subtype with hA
  have hAmem : ∀ g : G, g ∈ A ↔ ∃ hg : g ∈ V, θ ⟨g, hg⟩ ∈ Zs := by
    intro g
    simp only [hA, Subgroup.mem_map, Subgroup.mem_comap, Subgroup.coe_subtype]
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨a.2, ha⟩
    · rintro ⟨hg, hz⟩
      exact ⟨⟨g, hg⟩, hz, rfl⟩
  have hAV : A ≤ V := fun g hg => ((hAmem g).1 hg).1
  have hUC : U ≤ V ⊓ Subgroup.centralizer (L : Set G) := le_inf_centralizer_component hU.1 hL
  have hne1 : ∀ Z : Subgroup (Bar.Qbar L), Nat.card Z = 2 ^ n → ∃ z ∈ Z, z ≠ 1 := by
    intro Z hZc
    by_contra hcon
    push Not at hcon
    have h0 : Z = ⊥ := (Subgroup.eq_bot_iff_forall Z).2 hcon
    rw [h0, Subgroup.card_bot] at hZc
    have : 1 < 2 ^ n := Nat.one_lt_two_pow (by omega)
    omega
  have hcover : ∀ w ∈ omegaCenter (sylowBar T V L), ∃ a : ↥V, θ a = w := fun w hw => by
    have : w ∈ θ.range := hW ▸ hw
    exact this
  obtain ⟨zs, hzs, hzs1⟩ := hne1 Zs hcs
  obtain ⟨zl, hzl, hzl1⟩ := hne1 Zl hcl
  obtain ⟨a, ha⟩ := hcover zs (hZsZ hzs)
  obtain ⟨b, hb⟩ := hcover zl (hZlZ hzl)
  have haA : (a : G) ∈ A := (hAmem a).2 ⟨a.2, by simpa [ha] using hzs⟩
  have haC : (a : G) ∉ V ⊓ Subgroup.centralizer (L : Set G) := by
    intro hC'
    have := (theta_eq_one_iff hVN θ hθ hZ0 hperf a).2 hC'.2
    rw [ha] at this
    exact hzs1 this
  have hbA : (b : G) ∉ A := by
    intro hbA'
    obtain ⟨hbV, hbz⟩ := (hAmem b).1 hbA'
    have hbz' : θ b ∈ Zs := hbz
    have : zl ∈ Zs ⊓ Zl := ⟨hb ▸ hbz', hzl⟩
    rw [hinf, Subgroup.mem_bot] at this
    exact hzl1 this
  have hCA : V ⊓ Subgroup.centralizer (L : Set G) ≤ A := by
    rintro g ⟨hgV, hgC⟩
    refine (hAmem g).2 ⟨hgV, ?_⟩
    rw [(theta_eq_one_iff hVN θ hθ hZ0 hperf ⟨g, hgV⟩).2 hgC]
    exact Zs.one_mem
  refine ⟨A, lt_of_le_of_ne (hUC.trans hCA) ?_, lt_of_le_of_ne hAV ?_, ?_, ?_⟩
  · intro hUA
    apply haC
    apply hUC
    rw [hUA]
    exact haA
  · intro hAV'
    apply hbA
    rw [hAV']
    exact b.2
  ·
    have h1 : A.subgroupOf V = Zs.comap θ := by
      rw [hA, Subgroup.subgroupOf]
      exact Subgroup.comap_map_eq_self_of_injective Subtype.val_injective _
    have h2 : A.relIndex V = Zs.relIndex θ.range := by
      rw [Subgroup.relIndex, h1, ← Subgroup.relIndex_top_right, Subgroup.relIndex_comap,
        ← MonoidHom.range_eq_map]
    have h3 := Subgroup.relIndex_mul_card (H := Zs) (K := θ.range)
    have hcθ : Nat.card θ.range = 2 ^ (2 * n) := by rw [hW]; exact hcZ
    rw [inf_eq_left.2 (hW ▸ hZsZ), hcθ, hcs] at h3
    have h4 : Zs.relIndex θ.range = 2 ^ n := by
      have h5 : 2 ^ n * 2 ^ n = 2 ^ (2 * n) := by rw [← pow_add]; congr 1; omega
      exact Nat.eq_of_mul_eq_mul_right (Nat.two_pow_pos n) (h3.trans h5.symm)
    have h6 := E3.relIndex_eq_two_pow h.isPGroup_V A
    rw [h2, h4] at h6
    exact (Nat.pow_right_injective le_rfl h6).symm
  ·
    intro hle
    obtain ⟨y', hy'C, hy'N⟩ := IsConcreteLE.not_le_iff_exists.1 hcent
    obtain ⟨l, rfl⟩ := piBar_surjective (L := L) y'
    have hl : (l : G) ∈ L ⊓ Subgroup.centralizer (A : Set G) := by
      refine ⟨l.2, Subgroup.mem_centralizer_iff.2 fun g hg => ?_⟩
      obtain ⟨hgV, hgz⟩ := (hAmem g).1 hg
      have h1 := Subgroup.mem_centralizer_iff.1 hy'C _ hgz
      exact (comm_of_theta_comm hVN θ hθ hinj l ⟨g, hgV⟩ h1.symm).symm
    have hlX : (l : G) ∈ L ⊓ M := ⟨l.2, hle hl⟩
    rw [hXeq] at hlX
    exact hy'N ((mem_borOf_iff hZ).1 hlX).2

theorem case_of_sp4 (hInn : Ch1.EvenLieAutInner) (hmod : Ch1.SQTKCharTwoLie (Bar.Qbar L))
    (hV : CFSG.Open.IsElemAbelian 2 V) (h : HypE61 T M V) (hU : U ∈ gammaE64 V M)
    (hL : IsComponentIn L (Subgroup.centralizer (U : Set G))) (hZ0L : Subgroup.center ↥L = ⊥)
    {n : ℕ} (hn : 2 ≤ n) (hdata : E68Sp4Data (sylowBar T V L) n) (hBX : borOf T V L ≤ M)
    {P₁ P₂ : Subgroup G} (hsup : P₁ ⊔ P₂ = L)
    (honly : ∀ Y : Subgroup G, borOf T V L < Y → Y < L → Y = P₁ ∨ Y = P₂)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel ↥L .PSp 2 2 n) :
    E68Case2 hV T M U L := by
  classical
  have hZ2 := isPGroup_two_of_center_eq_bot hZ0L
  have hZ := center_le_sylow h hU hL hZ2
  have hq : CFSG.IsQuasisimple ↥L := BenderBranch.isQuasisimple_of_isComponentIn hL
  have hZ0 := center_qbar_eq_bot hq
  have hperf : Group.IsPerfect ↥L := hq.1
  have hLM : ¬ L ≤ M := not_le_of_component h hU.1 hL
  have hVN : V ≤ Subgroup.normalizer (L : Set G) := le_normalizer_of_component h hU hL
  obtain ⟨-, hres, hXN⟩ := sandwich h hU hL
  obtain ⟨θ, hθ, hθZ⟩ := exists_theta hInn hmod h hU hL
  set P := sylowBar T V L with hP
  obtain ⟨Zs, Zl, hZsZ, hZlZ, hinf, hsup', hcs, hcl, hinvs, hinvl, ⟨xs, hxsN, hxsZl, hxstr⟩,
    ⟨xl, hxlN, hxlZs, hxltr⟩, hautS, hautL, hcentS, hcentL⟩ := hdata.split
  have hsS : SingerHyp (Subgroup.normalizer (P : Set (Bar.Qbar L))) Zs xs :=
    ⟨hxsN, hinvs, fun a ha b hb _ hw =>
      ((mem_omegaCenter.1 (hZsZ hw)).2.1 _ (hdata.quot_comm a ha b hb)).symm, hxstr⟩
  have hlS : SingerHyp (Subgroup.normalizer (P : Set (Bar.Qbar L))) Zl xl :=
    ⟨hxlN, hinvl, fun a ha b hb _ hw =>
      ((mem_omegaCenter.1 (hZlZ hw)).2.1 _ (hdata.quot_comm a ha b hb)).symm, hxltr⟩
  have h3 : 3 ≤ 2 ^ n := by
    calc 3 ≤ 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have h3s : 3 ≤ Nat.card Zs := by rw [hcs]; exact h3
  have h3l : 3 ≤ Nat.card Zl := by rw [hcl]; exact h3
  have hBX' : borOf T V L ≤ L ⊓ M := le_inf borOf_le_left hBX
  have hWne : θ.range ≠ ⊥ :=
    theta_range_ne_bot h.isPGroup_V hVN θ hθ hZ0 hperf (mQuot_ne_zero_of_not_le h hLM)
  have hWle : θ.range ≤ omegaCenter P := by
    rintro _ ⟨a, rfl⟩
    exact hθZ a
  obtain ⟨ys, hys, hysx⟩ := exists_mem_borOf_of_mem_normalizer hZ hxsN
  obtain ⟨yl, hyl, hylx⟩ := exists_mem_borOf_of_mem_normalizer hZ hxlN
  have hWs : ∀ w ∈ θ.range, xs * w * xs⁻¹ ∈ θ.range := by
    intro w hw
    have := theta_range_invariant hVN θ hθ hZ0 (hBX' hys).1 (hXN (hBX' hys)) w hw
    rwa [hysx] at this
  have hWl : ∀ w ∈ θ.range, xl * w * xl⁻¹ ∈ θ.range := by
    intro w hw
    have := theta_range_invariant hVN θ hθ hZ0 (hBX' hyl).1 (hXN (hBX' hyl)) w hw
    rwa [hylx] at this
  have hC_ge : E3.mQuot V (V ⊓ Subgroup.centralizer (L : Set G)) ≤ E3.mQuot V U :=
    E3.mQuot_mono (le_inf_centralizer_component hU.1 hL)
  have hdecomp : (∀ w ∈ θ.range,
      (∀ b ∈ Subgroup.normalizer (P : Set (Bar.Qbar L)), b * w * b⁻¹ = w) → w = 1) →
      ⁅V, L ⊓ M⁆ ⊓ (V ⊓ Subgroup.centralizer (L : Set G)) = ⊥ ∧
        ⁅V, L ⊓ M⁆ ⊔ (V ⊓ Subgroup.centralizer (L : Set G)) = V := fun hfix => by
    obtain ⟨d1, d2⟩ := decomp_of_theta_fixed hV h hU hL hZ2 hBX' θ hθ hfix
    exact ⟨by rw [inf_comm]; exact d1, by rw [sup_comm]; exact d2⟩
  rcases eq_cases_of_invariant hsS hlS h3s h3l hZsZ hZlZ hsup' hxsZl hxlZs hWle hWne hWs hWl with
    hW | hW | hW
  ·
    obtain ⟨b1, b2, b3, b4, b5⟩ := case2b_of_Zx hV h hU hL hZ0L hn hBX θ hθ hW hsS hcs hautS
      hcentS hsup honly
    refine ⟨n, by omega, Or.inl ⟨hn, hmodel⟩, hC_ge, fun _ => hdecomp ?_, Or.inr ⟨b1, b2, b3, b4,
      b5⟩⟩
    intro w hw hfb
    rw [hW] at hw
    exact hsS.eq_one_of_fixed h3s hw (hfb xs hxsN)
  ·
    obtain ⟨b1, b2, b3, b4, b5⟩ := case2b_of_Zx hV h hU hL hZ0L hn hBX θ hθ hW hlS hcl hautL
      hcentL hsup honly
    refine ⟨n, by omega, Or.inl ⟨hn, hmodel⟩, hC_ge, fun _ => hdecomp ?_, Or.inr ⟨b1, b2, b3, b4,
      b5⟩⟩
    intro w hw hfb
    rw [hW] at hw
    exact hlS.eq_one_of_fixed h3l hw (hfb xl hxlN)
  ·
    have hCV : L ⊓ Subgroup.centralizer (V : Set G) ≤ borOf T V L := by
      rintro y ⟨hyL, hyC⟩
      refine (mem_borOf_iff hZ).2 ⟨hyL, hdata.centralizer_root ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      rw [← hW] at hw
      obtain ⟨a, rfl⟩ := hw
      have hcomm : (y : G) * a = a * y := (Subgroup.mem_centralizer_iff.1 hyC a a.2).symm
      exact (theta_comm_of_comm hVN θ hθ ⟨y, hyL⟩ a hcomm).symm
    have hPg2 : IsPGroup 2 (pgOf T V L) := h.isPGroup_Q.to_le inf_le_left
    have hsolvB := isSolvable_borOf hZ hPg2 hdata.quot_comm
    have hPX : pgOf T V L ≤ L ⊓ M :=
      le_inf pgOf_le_left (inf_le_left.trans (inf_le_right.trans h.centralizer_le))
    have hXB : L ⊓ M ≤ borOf T V L :=
      inf_le_borOf_of_residual hZ hPX (fun hh => hLM (hh ▸ inf_le_right)) hBX hsolvB
        (hres.trans hCV) hdata.not_solvable
    have hXeq : L ⊓ M = borOf T V L := le_antisymm hXB hBX'
    have hm2 : E3.mQuot V (V ⊓ Subgroup.centralizer (L : Set G)) = 2 * n :=
      mQuot_eq_of_card_range h.isPGroup_V hVN θ hθ hZ0 hperf (by rw [hW]; exact hdata.card_root)
    obtain ⟨A, hUA, hAV, hmA, hCA⟩ := exists_A_of_range_eq h hU hL hZ0L hn θ hθ hW hZsZ hZlZ hinf
      hcs hcl hdata.card_root hcentS hXeq
    refine ⟨n, by omega, Or.inl ⟨hn, hmodel⟩, hC_ge, fun _ => hdecomp ?_, Or.inl ⟨hXeq,
      Or.inl ⟨hm2, A, hUA, hAV, hmA, hCA⟩⟩⟩
    intro w hw hfb
    exact eq_one_of_fixed_both hsS hlS h3s h3l hZsZ hZlZ hsup' hxsZl hxlZs (hW ▸ hw)
      (hfb xs hxsN) (hfb xl hxlN)

end Geometry

end E68Proof

end E6

end CFSG.Quasithin
