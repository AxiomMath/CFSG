module

public import CFSG.LocalAnalysis.StandardType.FS81.TwD7QCanonAux

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Open CFSG.Assembly Subgroup
open scoped commutatorElement

private theorem closure_insert_eq_sup {G : Type*} [Group G] (a : G) (S : Set G) :
    Subgroup.closure (insert a S) = Subgroup.zpowers a ⊔ Subgroup.closure S := by
  refine le_antisymm ?_ ?_
  · refine (Subgroup.closure_le _).mpr ?_
    rintro x (hx | hx)
    · rw [hx]
      exact Subgroup.mem_sup_left (Subgroup.mem_zpowers a)
    · exact Subgroup.mem_sup_right (Subgroup.subset_closure hx)
  · refine sup_le ?_ (Subgroup.closure_mono (Set.subset_insert _ _))
    rw [Subgroup.zpowers_le]
    exact Subgroup.subset_closure (Set.mem_insert _ _)

private theorem subgroupOf_closure_eq {G : Type*} [Group G] {H : Subgroup G} {S : Set G}
    (hS : S ⊆ H) :
    (Subgroup.closure S).subgroupOf H = Subgroup.closure ((Subtype.val : H → G) ⁻¹' S) := by
  refine le_antisymm ?_ ?_
  · intro x hx
    rw [Subgroup.mem_subgroupOf] at hx
    have hclosure : Subgroup.closure S ≤
        (Subgroup.closure ((Subtype.val : H → G) ⁻¹' S)).map H.subtype := by
      refine (Subgroup.closure_le _).mpr ?_
      intro s hs
      have hs' : (⟨s, hS hs⟩ : H) ∈ (Subtype.val : H → G) ⁻¹' S := hs
      exact Subgroup.mem_map.mpr
        ⟨⟨s, hS hs⟩, Subgroup.subset_closure hs', rfl⟩
    obtain ⟨y, hy, hyeq⟩ := Subgroup.mem_map.mp (hclosure hx)
    have : x = y := Subtype.ext hyeq.symm
    rwa [this]
  · refine (Subgroup.closure_le _).mpr ?_
    intro x hx
    exact Subgroup.mem_subgroupOf.mpr (Subgroup.subset_closure hx)

private theorem zpowers_mul_inf_K_eq_bot {G : Type} [Group G] [Finite G] {b₀ : G}
    {K E : Subgroup G} (hstd : StdAssumptions b₀ K E Row.twD7)
    {B : Basis3 G 8} (hB : Adapted B b₀ K E) :
    Subgroup.zpowers (B.b 0 * B.b 1) ⊓ K = ⊥ := by
  have hb₀ : B.b 0 = b₀ := hB.2.1
  have hb₁K : B.b 1 ∈ K := hB.2.2 1 (by decide)
  have hdisj0 : Disjoint (Subgroup.zpowers b₀) K :=
    disjoint_zpowers_of_center hstd.2.1.1.2.1 hstd.2.1.1.2.2.2.1
  have hβ3 : orderOf (B.b 0 * B.b 1) = 3 := by
    rw [← B.twD7Beta_b_zero]
    exact B.twD7Beta.ord 0
  rw [eq_bot_iff]
  intro x hx
  have hdvd : Nat.card ↥(Subgroup.zpowers (B.b 0 * B.b 1) ⊓ K) ∣ 3 := by
    have h := Subgroup.card_dvd_of_le (inf_le_left :
      Subgroup.zpowers (B.b 0 * B.b 1) ⊓ K ≤ Subgroup.zpowers (B.b 0 * B.b 1))
    rwa [Nat.card_zpowers, hβ3] at h
  rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
  · rw [Subgroup.card_eq_one.mp h1] at hx
    simpa using hx
  · exfalso
    have hEq : Subgroup.zpowers (B.b 0 * B.b 1) ⊓ K =
        Subgroup.zpowers (B.b 0 * B.b 1) :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (by
        have hle : Nat.card ↥(Subgroup.zpowers (B.b 0 * B.b 1)) ≤
            Nat.card ↥(Subgroup.zpowers (B.b 0 * B.b 1) ⊓ K) := by
          rw [Nat.card_zpowers, hβ3, h3]
        exact hle)
    have hβK : B.b 0 * B.b 1 ∈ K := by
      have hmem : B.b 0 * B.b 1 ∈ Subgroup.zpowers (B.b 0 * B.b 1) ⊓ K := by
        rw [hEq]
        exact Subgroup.mem_zpowers _
      exact (Subgroup.mem_inf.mp hmem).2
    have hb₀K : b₀ ∈ K := by
      have h := K.mul_mem hβK (K.inv_mem hb₁K)
      rw [mul_inv_cancel_right] at h
      rwa [← hb₀]
    have hb₀1 : b₀ = 1 :=
      Subgroup.disjoint_def.mp hdisj0 (Subgroup.mem_zpowers b₀) hb₀K
    have hord : orderOf b₀ = 3 := hstd.2.1.1.1
    rw [hb₀1, orderOf_one] at hord
    exact absurd hord (by decide)

open TwD7Q in
theorem nonempty_mulEquiv_img_m0_twD7 {G : Type} [Group G] [Finite G] {b₀ : G}
    {K E : Subgroup G} (hstd : StdAssumptions b₀ K E Row.twD7)
    {B : Basis3 G 8} (hB : Adapted B b₀ K E) (hrec : RecOutTwD7 B b₀) :
    Nonempty (↥(img (B.b 0 * B.b 1) ⁅Subgroup.centralizer ({B.b 1} : Set G) ⊓ K,
      Subgroup.centralizer ({B.b 1} : Set G) ⊓ K⁆) ≃*
      ↥⁅Subgroup.centralizer ({B.b 1} : Set G) ⊓ K,
        Subgroup.centralizer ({B.b 1} : Set G) ⊓ K⁆) := by
  classical
  let C : Subgroup G := Subgroup.centralizer ({B.b 1} : Set G) ⊓ K
  let M : Subgroup G := ⁅C, C⁆
  have hMleC : M ≤ C := Subgroup.commutator_le_self C
  have hMleK : M ≤ K := hMleC.trans inf_le_right
  have hMleCen : M ≤ cen (B.b 0 * B.b 1) := by
    have h := (commutator_centralizer_le_beta_of_std_twD7 hstd B).2
    simpa only [hB.2.1] using h
  have hβK : Subgroup.zpowers (B.b 0 * B.b 1) ⊓ K = ⊥ :=
    zpowers_mul_inf_K_eq_bot hstd hB
  have hdisjM : M ⊓ Subgroup.zpowers (B.b 0 * B.b 1) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hxK : x ∈ K := hMleK hx.1
    have hxZ : x ∈ Subgroup.zpowers (B.b 0 * B.b 1) := hx.2
    have hmem : x ∈ Subgroup.zpowers (B.b 0 * B.b 1) ⊓ K := ⟨hxZ, hxK⟩
    rw [hβK] at hmem
    simpa using hmem
  let f : ↥(M.subgroupOf (cen (B.b 0 * B.b 1))) →*
      ↥(img (B.b 0 * B.b 1) M) :=
    { toFun := fun x => ⟨pr (B.b 0 * B.b 1) x, pr_mem_img (mem_subgroupOf.mp x.2)⟩
      map_one' := by ext; simp
      map_mul' := by intro x y; ext; simp }
  have hf_inj : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    have h := (pr_eq_pr_iff (β := B.b 0 * B.b 1) x y).mp (congrArg Subtype.val hxy)
    have hmemM : (x : G)⁻¹ * (y : G) ∈ M :=
      M.mul_mem (M.inv_mem (mem_subgroupOf.mp x.2)) (mem_subgroupOf.mp y.2)
    have hbot : (x : G)⁻¹ * (y : G) = 1 := by
      have hmem : (x : G)⁻¹ * (y : G) ∈
          M ⊓ Subgroup.zpowers (B.b 0 * B.b 1) := ⟨hmemM, h⟩
      rw [hdisjM] at hmem
      simpa using hmem
    exact inv_mul_eq_one.mp hbot
  have hf_surj : Function.Surjective f := by
    rintro ⟨q, hq⟩
    obtain ⟨x, hx, hq⟩ := mem_img_iff.mp hq
    exact ⟨⟨x, hx⟩, Subtype.ext hq⟩
  exact ⟨(MulEquiv.ofBijective f ⟨hf_inj, hf_surj⟩).symm.trans
    (Subgroup.subgroupOfEquivOfLe hMleCen)⟩


open TwD7Q in
theorem twD7Quot_b_succ_mem_img_m0 {G : Type} [Group G] [Finite G] {b₀ : G}
    {K E : Subgroup G} (hstd : StdAssumptions b₀ K E Row.twD7)
    {B : Basis3 G 8} (hB : Adapted B b₀ K E) (hrec : RecOutTwD7 B b₀) (j : Fin 6) :
    B.twD7Quot.b j.succ ∈ img (B.b 0 * B.b 1)
      ⁅Subgroup.centralizer ({B.b 1} : Set G) ⊓ K,
        Subgroup.centralizer ({B.b 1} : Set G) ⊓ K⁆ := by
  rw [← B.pr_b_succ_succ_twD7Quot j]
  exact pr_mem_img (tail_mem_commutator_centralizer_of_std_twD7 hstd B hB hrec j)

open TwD7Q in
theorem canonPosition_twD7Quot {G : Type} [Group G] [Finite G] {b₀ : G}
    {K E : Subgroup G} (hstd : StdAssumptions b₀ K E Row.twD7)
    {B : Basis3 G 8} (hB : Adapted B b₀ K E) (hrec : RecOutTwD7 B b₀) :
    CanonPosition (B.twD7Quot.b 0) (img (B.b 0 * B.b 1)
      ⁅Subgroup.centralizer ({B.b 1} : Set G) ⊓ K,
        Subgroup.centralizer ({B.b 1} : Set G) ⊓ K⁆) B.twD7Quot.span Row.D6 := by
  classical
  let C : Subgroup G := Subgroup.centralizer ({B.b 1} : Set G) ⊓ K
  let M : Subgroup G := ⁅C, C⁆
  let T : Subgroup G := Subgroup.closure (Set.range fun j : Fin 6 => B.b j.succ.succ)
  have hMleC : M ≤ C := Subgroup.commutator_le_self C
  have hMleK : M ≤ K := hMleC.trans inf_le_right
  have hMleC1 : M ≤ Subgroup.centralizer ({B.b 1} : Set G) := hMleC.trans inf_le_left
  have hMleCen : M ≤ cen (B.b 0 * B.b 1) := by
    have h := (commutator_centralizer_le_beta_of_std_twD7 hstd B).2
    simpa only [hB.2.1] using h
  have hrec' : RecOutTwD7 B (B.b 0) := hB.2.1.symm ▸ hrec
  have hb₀ : B.b 0 = b₀ := hB.2.1
  have hTleE : T ≤ E := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro _ ⟨j, rfl⟩
    rw [← hB.1]
    exact B.b_mem_span _
  have hTleK : T ≤ K := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro _ ⟨j, rfl⟩
    exact hB.2.2 _ (Fin.succ_ne_zero _)
  have hTleM : T ≤ M := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro _ ⟨j, rfl⟩
    exact tail_mem_commutator_centralizer_of_std_twD7 hstd B hB hrec j
  have hTleCen : T ≤ cen (B.b 0 * B.b 1) := hTleM.trans hMleCen
  have hT7K : (B.dropFirst).span ≤ K := by
    rw [B.dropFirst_span]
    refine (Subgroup.closure_le _).mpr ?_
    rintro _ ⟨i, rfl⟩
    exact hB.2.2 _ (Fin.succ_ne_zero _)
  have hcardA : Nat.card ↥(E ⊓ K) = 3 ^ 7 := by
    have h := hstd.2.2.2.2.2.2.1
    simpa [Row.n] using h
  have hA : E ⊓ K = (B.dropFirst).span := by
    have hle : (B.dropFirst).span ≤ E ⊓ K :=
      le_inf (hB.1 ▸ B.dropFirst_span_le) hT7K
    have hcard7 : Nat.card ↥(B.dropFirst).span = 3 ^ 7 := Basis3.card_span B.dropFirst
    exact (Subgroup.eq_of_le_of_card_ge (H := (B.dropFirst).span) (K := E ⊓ K) hle (by
      change Nat.card ↥(E ⊓ K) ≤ Nat.card ↥(B.dropFirst).span
      omega)).symm
  have hrange : Set.range (fun i : Fin 7 => B.b i.succ) =
      insert (B.b 1) (Set.range fun j : Fin 6 => B.b j.succ.succ) := by
    have htail : Set.range (Fin.tail (fun i : Fin 7 => B.b i.succ)) =
        Set.range (fun j : Fin 6 => B.b j.succ.succ) := by
      have hfun : Fin.tail (fun i : Fin 7 => B.b i.succ) =
          (fun j : Fin 6 => B.b j.succ.succ) := by
        funext j
        rfl
      rw [hfun]
    rw [Fin.range_fin_succ, htail]
    exact congrArg (fun x => insert x (Set.range fun j : Fin 6 => B.b j.succ.succ))
      (congrArg B.b (Fin.succ_zero_eq_one' (n := 7)))
  have hA1 : E ⊓ K = Subgroup.zpowers (B.b 1) ⊔ T := by
    rw [hA, show (B.dropFirst).span =
      Subgroup.closure (Set.range fun i : Fin 7 => B.b i.succ) from rfl,
      hrange, closure_insert_eq_sup]
  have hcommZT : ∀ z ∈ Subgroup.zpowers (B.b 1), ∀ t ∈ T, z * t = t * z := by
    intro z hz t ht
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    have htC : t ∈ Subgroup.centralizer ({B.b 1} : Set G) := hMleC1 (hTleM ht)
    have hc : Commute (B.b 1) t :=
      (Subgroup.mem_centralizer_singleton_iff.mp htC).symm
    exact (hc.zpow_left n).eq
  have hEM : E ⊓ M = T := by
    refine le_antisymm ?_ (le_inf hTleE hTleM)
    intro x hx
    obtain ⟨hxE, hxM⟩ := Subgroup.mem_inf.mp hx
    have hxa : x ∈ Subgroup.zpowers (B.b 1) ⊔ T := by
      rw [← hA1]
      exact ⟨hxE, hMleK hxM⟩
    obtain ⟨z, hz, t, ht, hxt⟩ := (Subgroup.mem_sup_iff_of_forall_commute hcommZT).mp hxa
    have hzM : z ∈ M := by
      have hz : z = x * t⁻¹ := by rw [hxt]; group
      rw [hz]
      exact M.mul_mem hxM (M.inv_mem (hTleM ht))
    have hdisj1 : Disjoint (Subgroup.zpowers (B.b 1)) M :=
      (centralizer_inf_eq_zpowers_sup_commutator_twD7 hstd hB hrec).2.2
    have hz1 : z = 1 := Subgroup.disjoint_def.mp hdisj1 hz hzM
    rw [hxt, hz1, one_mul]
    exact ht
  have himgT : img (B.b 0 * B.b 1) T =
      Subgroup.closure (Set.range fun j : Fin 6 => B.twD7Quot.b j.succ) := by
    change ((Subgroup.closure (Set.range fun j : Fin 6 => B.b j.succ.succ)).subgroupOf
        (cen (B.b 0 * B.b 1))).map (pr (B.b 0 * B.b 1)) = _
    rw [subgroupOf_closure_eq (fun x hx => hTleCen (Subgroup.subset_closure hx)),
      MonoidHom.map_closure]
    congr 1
    ext q
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨j, hj⟩ := hx
      refine ⟨j, ?_⟩
      have hx' : x = ⟨B.b j.succ.succ, B.b_mem_cen_twD7 _⟩ := Subtype.ext hj.symm
      rw [hx', B.pr_b_succ_succ_twD7Quot j]
    · rintro ⟨j, rfl⟩
      exact ⟨⟨B.b j.succ.succ, B.b_mem_cen_twD7 _⟩, ⟨j, rfl⟩,
        B.pr_b_succ_succ_twD7Quot j⟩
  have hEbar : B.twD7Quot.span = img (B.b 0 * B.b 1) E := by
    rw [B.twD7Quot_span, hB.1]
  have hEbar_sup : B.twD7Quot.span =
      Subgroup.zpowers (B.twD7Quot.b 0) ⊔ img (B.b 0 * B.b 1) T := by
    change Subgroup.closure (Set.range B.twD7Quot.b) = _
    have hrange7 : Set.range (fun i : Fin 7 => B.twD7Quot.b i) =
        insert (B.twD7Quot.b 0)
          (Set.range fun j : Fin 6 => B.twD7Quot.b j.succ) := by
      have htail : Set.range (Fin.tail (fun i : Fin 7 => B.twD7Quot.b i)) =
          Set.range (fun j : Fin 6 => B.twD7Quot.b j.succ) := by
        have hfun : Fin.tail (fun i : Fin 7 => B.twD7Quot.b i) =
            (fun j : Fin 6 => B.twD7Quot.b j.succ) := by
          funext j
          rfl
        rw [hfun]
      rw [Fin.range_fin_succ, htail]
    rw [show Set.range B.twD7Quot.b = Set.range (fun i : Fin 7 => B.twD7Quot.b i) from rfl,
      hrange7, closure_insert_eq_sup, himgT]
  have hβE : B.b 0 * B.b 1 ∈ E := by
    have h := B.twD7Beta.b_mem_span 0
    rw [B.twD7Beta_span, hB.1] at h
    simpa only [B.twD7Beta_b_zero] using h
  have hEq : B.twD7Quot.span ⊓ img (B.b 0 * B.b 1) M =
      img (B.b 0 * B.b 1) T := by
    refine le_antisymm ?_ ?_
    · rintro y ⟨hyE, hyM⟩
      rw [hEbar] at hyE
      obtain ⟨x, hxE, hxy⟩ := mem_img_iff.mp hyE
      obtain ⟨m, hmM, hmy⟩ := mem_img_iff.mp hyM
      have hpr : (x : G)⁻¹ * (m : G) ∈ Subgroup.zpowers (B.b 0 * B.b 1) := by
        refine (pr_eq_pr_iff (β := B.b 0 * B.b 1) x m).mp ?_
        rw [hxy, hmy]
      have hmE : (m : G) ∈ E := by
        have hzE : (x : G)⁻¹ * (m : G) ∈ E := (Subgroup.zpowers_le.mpr hβE) hpr
        have hm : (m : G) = (x : G) * ((x : G)⁻¹ * (m : G)) := by group
        rw [hm]
        exact E.mul_mem hxE hzE
      have hmT : (m : G) ∈ T := by
        have hmem : (m : G) ∈ E ⊓ M := ⟨hmE, hmM⟩
        rwa [hEM] at hmem
      exact mem_img_iff.mpr ⟨m, hmT, hmy⟩
    · rintro y ⟨m, hmT, rfl⟩
      refine ⟨?_, pr_mem_img (hTleM hmT)⟩
      rw [hEbar]
      exact img_mono hTleE (mem_img_iff.mpr ⟨m, hmT, rfl⟩)
  have hcardImgT : Nat.card ↥(img (B.b 0 * B.b 1) T) = 3 ^ 6 := by
    rw [himgT, ← Basis3.dropFirst_span B.twD7Quot]
    exact Basis3.card_span B.twD7Quot.dropFirst
  have hdisj : Disjoint (Subgroup.zpowers (B.twD7Quot.b 0))
      (B.twD7Quot.span ⊓ img (B.b 0 * B.b 1) M) := by
    rw [hEq, Subgroup.disjoint_def]
    intro x hxZ hxT
    have hxT' : x ∈ B.twD7Quot.dropFirst.span := by
      rw [Basis3.dropFirst_span B.twD7Quot, ← himgT]
      exact hxT
    obtain ⟨e, he⟩ := B.twD7Quot.dropFirst.exists_vec_eq hxT'
    have hxe : B.twD7Quot.vec (Fin.cons 0 e) = x :=
      (Basis3.vec_cons_zero (B := B.twD7Quot) e).trans he
    have hz : B.twD7Quot.vec (Fin.cons 0 e) ∈ Subgroup.zpowers (B.twD7Quot.b 0) := by
      rw [hxe]
      exact hxZ
    have hzero := Basis3.eq_zero_of_vec_mem_zpowers_of_coord_zero B.twD7Quot
      (e := Fin.cons 0 e) rfl hz
    rw [hzero] at hxe
    rw [← hxe]
    exact Basis3.vec_zero B.twD7Quot
  have hself : Subgroup.centralizer
      ((B.twD7Quot.span ⊓ img (B.b 0 * B.b 1) M) : Set (Q (B.b 0 * B.b 1))) ⊓
        img (B.b 0 * B.b 1) M = B.twD7Quot.span ⊓ img (B.b 0 * B.b 1) M := by
    refine le_antisymm ?_ ?_
    · rintro q ⟨hqC, hqM⟩
      rw [hEq]
      obtain ⟨m, hmM, rfl⟩ := mem_img_iff.mp hqM
      have hmK : (m : G) ∈ K := hMleK hmM
      have hmCentT : ∀ t ∈ T, (m : G) * t = t * (m : G) := by
        intro t ht
        have htcen : t ∈ cen (B.b 0 * B.b 1) := hTleCen ht
        have hcomm : pr (B.b 0 * B.b 1) ⟨t, htcen⟩ * pr (B.b 0 * B.b 1) m =
            pr (B.b 0 * B.b 1) m * pr (B.b 0 * B.b 1) ⟨t, htcen⟩ :=
          (Subgroup.mem_centralizer_iff.mp hqC) (pr (B.b 0 * B.b 1) ⟨t, htcen⟩)
            (Subgroup.mem_inf.mpr ⟨by
                rw [hEbar]
                exact mem_img_iff.mpr ⟨⟨t, htcen⟩, hTleE ht, rfl⟩,
              mem_img_iff.mpr ⟨⟨t, htcen⟩, hTleM ht, rfl⟩⟩)
        have h1 : (t : G)⁻¹ * ((m : G) * t * (m : G)⁻¹) ∈
            Subgroup.zpowers (B.b 0 * B.b 1) := (pr_commute_iff (β := B.b 0 * B.b 1) _ _).mp hcomm
        have h2 : (t : G)⁻¹ * ((m : G) * t * (m : G)⁻¹) ∈ K :=
          K.mul_mem (K.inv_mem (hTleK ht))
            (K.mul_mem (K.mul_mem hmK (hTleK ht)) (K.inv_mem hmK))
        have h3 : (t : G)⁻¹ * ((m : G) * t * (m : G)⁻¹) = 1 := by
          have hmem : (t : G)⁻¹ * ((m : G) * t * (m : G)⁻¹) ∈
              Subgroup.zpowers (B.b 0 * B.b 1) ⊓ K := ⟨h1, h2⟩
          rw [zpowers_mul_inf_K_eq_bot hstd hB] at hmem
          simpa using hmem
        have h4 : (m : G) * t * (m : G)⁻¹ = t := by
          have h := congrArg (fun y => t * y) h3
          simpa [mul_assoc] using h
        calc (m : G) * t = ((m : G) * t * (m : G)⁻¹) * (m : G) := by group
          _ = t * (m : G) := by rw [h4]
      have hmC1 : Commute (m : G) (B.b 1) :=
        Subgroup.mem_centralizer_singleton_iff.mp (hMleC1 hmM)
      have hmCentA : ∀ y ∈ E ⊓ K, (m : G) * y = y * (m : G) := by
        intro y hy
        rw [hA1] at hy
        obtain ⟨z, hz, t, ht, rfl⟩ :=
          (Subgroup.mem_sup_iff_of_forall_commute hcommZT).mp hy
        have hzComm : (m : G) * z = z * (m : G) := by
          obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
          exact (hmC1.zpow_right n).eq
        calc (m : G) * (z * t) = ((m : G) * z) * t := by group
          _ = (z * (m : G)) * t := by rw [hzComm]
          _ = z * ((m : G) * t) := by group
          _ = z * (t * (m : G)) := by rw [hmCentT t ht]
          _ = (z * t) * (m : G) := by group
      have hmemC : (m : G) ∈ Subgroup.centralizer ((E ⊓ K : Subgroup G) : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        exact (hmCentA y hy).symm
      have hselfA : Subgroup.centralizer ((E ⊓ K : Subgroup G) : Set G) ⊓ K = E ⊓ K :=
        hstd.2.2.2.2.2.2.2
      have hmemA : (m : G) ∈ E ⊓ K := by
        have hmem : (m : G) ∈
            Subgroup.centralizer ((E ⊓ K : Subgroup G) : Set G) ⊓ K := ⟨hmemC, hmK⟩
        rwa [hselfA] at hmem
      have hmT : (m : G) ∈ T := by
        have hmem : (m : G) ∈ E ⊓ M := ⟨(Subgroup.mem_inf.mp hmemA).1, hmM⟩
        rwa [hEM] at hmem
      exact mem_img_iff.mpr ⟨m, hmT, rfl⟩
    · intro a ha
      refine Subgroup.mem_inf.mpr ⟨?_, ha.2⟩
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      exact congrArg Subtype.val ((Basis3.isElemAbelian_span B.twD7Quot).1.is_comm.comm
        ⟨x, hx.1⟩ ⟨a, ha.1⟩)
  have hrow : IsRow Row.D6 (img (B.b 0 * B.b 1) M) := by
    obtain ⟨e0⟩ := nonempty_mulEquiv_img_m0_twD7 hstd hB hrec
    obtain ⟨eD⟩ := nonempty_mulEquiv_om12_m0_twD7 hstd hB hrec
    exact (isRow_D6_of_mulEquiv_om12 (e0.trans eD)).1
  have hcard : Nat.card ↥(B.twD7Quot.span ⊓ img (B.b 0 * B.b 1) M) = 3 ^ Row.D6.n := by
    rw [hEq]
    simpa [Row.n] using hcardImgT
  have hsup : Subgroup.zpowers (B.twD7Quot.b 0) ⊔
      (B.twD7Quot.span ⊓ img (B.b 0 * B.b 1) M) = B.twD7Quot.span := by
    rw [hEq, ← hEbar_sup]
  have hmax : IsMaxElemAb3 (img (B.b 0 * B.b 1) M)
      (B.twD7Quot.span ⊓ img (B.b 0 * B.b 1) M) := by
    refine ⟨inf_le_right, (Basis3.isElemAbelian_span B.twD7Quot).mono inf_le_left, ?_⟩
    intro D hDM hD hle
    have hDcent : D ≤ Subgroup.centralizer
        ((B.twD7Quot.span ⊓ img (B.b 0 * B.b 1) M) : Set (Q (B.b 0 * B.b 1))) := by
      intro d hd
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      exact congrArg Subtype.val (hD.1.is_comm.comm ⟨a, hle ha⟩ ⟨d, hd⟩)
    have hDle : D ≤ Subgroup.centralizer
        ((B.twD7Quot.span ⊓ img (B.b 0 * B.b 1) M) : Set (Q (B.b 0 * B.b 1))) ⊓
          img (B.b 0 * B.b 1) M :=
      le_inf hDcent hDM
    rw [hself] at hDle
    exact le_antisymm hDle hle
  exact ⟨hrow, hdisj, hsup, hmax, hcard, hself⟩

end CFSG.StandardType.FrameRoute.FS81
