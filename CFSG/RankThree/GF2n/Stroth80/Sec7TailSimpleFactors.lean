module

public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.CGT.Timmesfeld75.Defs
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.Monster.B.Fischer.Fi22Order
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.RankThree.GF2n.Stroth80

open Subgroup CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank

structure SimpleFactors {Y : Type} [Group Y] {ι : Type} (Gs : Subgroup Y)
    (X : ι → Subgroup Y) : Prop where
  gnormal : ∀ y : Y, ∀ g ∈ Gs, y * g * y⁻¹ ∈ Gs
  le : ∀ i, X i ≤ Gs
  normal : ∀ i, ∀ g ∈ Gs, ∀ x ∈ X i, g * x * g⁻¹ ∈ X i
  comm : ∀ i j, i ≠ j → ∀ x ∈ X i, ∀ y ∈ X j, x * y = y * x
  gen : ⨆ i, X i = Gs
  simple : ∀ i, IsSimpleGroup ↥(X i)
  nonab : ∀ i, ∃ a ∈ X i, ∃ b ∈ X i, a * b ≠ b * a
  centre : ∀ z ∈ Gs, (∀ g ∈ Gs, z * g = g * z) → z = 1

structure IsProj {Y : Type} [Group Y] {ι : Type} (Gs : Subgroup Y) (X : ι → Subgroup Y)
    (π : ι → ↥Gs →* Y) : Prop where
  mem : ∀ i (g : ↥Gs), π i g ∈ X i
  self : ∀ i (x : ↥Gs), (x : Y) ∈ X i → π i x = x
  other : ∀ i j, i ≠ j → ∀ x : ↥Gs, (x : Y) ∈ X j → π i x = 1
  inj : ∀ g h : ↥Gs, (∀ i, π i g = π i h) → g = h
  surj : ∀ a : ι → Y, (∀ i, a i ∈ X i) → ∃ g : ↥Gs, ∀ i, π i g = a i

theorem exists_isProj {Y : Type} [Group Y] {ι : Type} [Fintype ι] [DecidableEq ι]
    {Gs : Subgroup Y} {X : ι → Subgroup Y} (h : SimpleFactors Gs X) :
    ∃ π : ι → ↥Gs →* Y, IsProj Gs X π := by
  have hind : iSupIndep X := by
    rw [iSupIndep_def]
    intro i
    rw [disjoint_iff, eq_bot_iff]
    intro z hz
    obtain ⟨hzi, hzM⟩ := Subgroup.mem_inf.mp hz
    have hM : (⨆ (j) (_ : j ≠ i), X j) ≤ Subgroup.centralizer (X i : Set Y) := by
      refine iSup_le fun j => iSup_le fun hj => ?_
      intro w hw
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      exact (h.comm j i hj w hw x hx).symm
    have hzc : z ∈ Subgroup.centralizer (X i : Set Y) := hM hzM
    have hall : Gs ≤ Subgroup.centralizer ({z} : Set Y) := by
      rw [← h.gen]
      refine iSup_le fun j => ?_
      by_cases hji : j = i
      · rw [hji]
        intro g hg
        rw [Subgroup.mem_centralizer_iff]
        intro s hs
        rw [Set.mem_singleton_iff] at hs
        rw [hs]
        exact (Subgroup.mem_centralizer_iff.mp hzc g hg).symm
      · intro g hg
        rw [Subgroup.mem_centralizer_iff]
        intro s hs
        rw [Set.mem_singleton_iff] at hs
        rw [hs]
        exact h.comm i j (Ne.symm hji) z hzi g hg
    have hz1 : z = 1 := h.centre z (h.le i hzi) (fun g hg =>
      Subgroup.mem_centralizer_iff.mp (hall hg) z (Set.mem_singleton z))
    rw [Subgroup.mem_bot]
    exact hz1
  have hcomm : Pairwise fun i j : ι => ∀ x y : Y, x ∈ X i → y ∈ X j → Commute x y := by
    intro i j hij x y hx hy
    exact h.comm i j hij x hx y hy
  have hrange : (Subgroup.noncommPiCoprod hcomm).range = Gs := by
    rw [Subgroup.noncommPiCoprod_range, h.gen]
  obtain ⟨ψ, hψ⟩ : ∃ ψ : (∀ i, ↥(X i)) ≃* ↥Gs,
      ∀ f : ∀ i, ↥(X i), ((ψ f : ↥Gs) : Y) = Subgroup.noncommPiCoprod hcomm f :=
    ⟨(MonoidHom.ofInjective
      (Subgroup.injective_noncommPiCoprod_of_iSupIndep (hcomm := hcomm) hind)).trans
      (MulEquiv.subgroupCongr hrange), fun f => rfl⟩
  obtain ⟨π, hπ⟩ : ∃ π : ι → ↥Gs →* Y, ∀ i g, π i g = ((ψ.symm g i : ↥(X i)) : Y) :=
    ⟨fun i => (X i).subtype.comp ((Pi.evalMonoidHom (fun k => ↥(X k)) i).comp
      ψ.symm.toMonoidHom), fun i g => rfl⟩
  have hsingle : ∀ i (x : ↥Gs) (hx : (x : Y) ∈ X i),
      ψ.symm x = Pi.mulSingle i (⟨(x : Y), hx⟩ : ↥(X i)) := by
    intro i x hx
    rw [MulEquiv.symm_apply_eq]
    apply Subtype.ext
    rw [hψ, Subgroup.noncommPiCoprod_mulSingle]
  refine ⟨π, ?_, ?_, ?_, ?_, ?_⟩
  · intro i g
    rw [hπ]
    exact (ψ.symm g i).2
  · intro i x hx
    rw [hπ, hsingle i x hx, Pi.mulSingle_eq_same]
  · intro i j hij x hx
    rw [hπ, hsingle j x hx, Pi.mulSingle_eq_of_ne hij]
    rfl
  · intro g g' hgg'
    apply ψ.symm.injective
    funext i
    apply Subtype.ext
    have hi := hgg' i
    rw [hπ, hπ] at hi
    exact hi
  · intro a ha
    refine ⟨ψ (fun i => ⟨a i, ha i⟩), fun i => ?_⟩
    rw [hπ, MulEquiv.symm_apply_apply]

theorem SimpleFactors.injective {Y : Type} [Group Y] {ι : Type} {Gs : Subgroup Y}
    {X : ι → Subgroup Y} (h : SimpleFactors Gs X) : Function.Injective X := by
  intro i j hij
  by_contra hne
  obtain ⟨a, ha, b, hb, hab⟩ := h.nonab i
  apply hab
  exact h.comm i j hne a ha b (by rw [← hij]; exact hb)

theorem le_of_simple_normalized_inter {Y : Type} [Group Y] (A B : Subgroup Y) [IsSimpleGroup ↥B]
    (hA : ∀ b ∈ B, ∀ a ∈ A ⊓ B, b * a * b⁻¹ ∈ A) (hne : A ⊓ B ≠ ⊥) : B ≤ A := by
  have hn : ((A ⊓ B).subgroupOf B).Normal := by
    rw [Subgroup.normal_subgroupOf_iff inf_le_right]
    intro k b hk hb
    exact ⟨hA b hb k hk, B.mul_mem (B.mul_mem hb hk.2) (B.inv_mem hb)⟩
  rcases Subgroup.Normal.eq_bot_or_eq_top ((A ⊓ B).subgroupOf B) with h1 | h1
  · exfalso
    apply hne
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    have hxB : x ∈ B := hx.2
    have hmem : (⟨x, hxB⟩ : ↥B) ∈ (A ⊓ B).subgroupOf B := Subgroup.mem_subgroupOf.mpr hx
    rw [h1, Subgroup.mem_bot] at hmem
    exact congrArg Subtype.val hmem
  · intro b hb
    have hmem : (⟨b, hb⟩ : ↥B) ∈ (A ⊓ B).subgroupOf B := by
      rw [h1]
      exact Subgroup.mem_top _
    exact (Subgroup.mem_subgroupOf.mp hmem).1

theorem conjSubgroup_eq_imp_eq {Y : Type} [Group Y] {A B : Subgroup Y} (g : Y)
    (hc : conjSubgroup g A = conjSubgroup g B) : A = B := by
  have key : ∀ C D : Subgroup Y, conjSubgroup g C = conjSubgroup g D → C ≤ D := by
    intro C D hCD x hx
    have e : g⁻¹ * (g * x * g⁻¹) * g = x := by group
    have h1 : g * x * g⁻¹ ∈ conjSubgroup g C := by
      rw [mem_conjSubgroup, e]
      exact hx
    rw [hCD, mem_conjSubgroup, e] at h1
    exact h1
  exact le_antisymm (key A B hc) (key B A hc.symm)

theorem factor_conj_exists {Y : Type} [Group Y] {ι : Type} {Gs : Subgroup Y}
    {X : ι → Subgroup Y} (h : SimpleFactors Gs X) (y : Y) (i : ι) :
    ∃ j, conjSubgroup y (X i) = X j := by
  have hMG : conjSubgroup y (X i) ≤ Gs := by
    intro m hm
    rw [mem_conjSubgroup] at hm
    have h1 := h.gnormal y _ (h.le i hm)
    have e : y * (y⁻¹ * m * y) * y⁻¹ = m := by group
    rwa [e] at h1
  have hMn : ∀ g ∈ Gs, ∀ m ∈ conjSubgroup y (X i), g * m * g⁻¹ ∈ conjSubgroup y (X i) := by
    intro g hg m hm
    rw [mem_conjSubgroup] at hm ⊢
    have hg' : y⁻¹ * g * y ∈ Gs := by
      have h1 := h.gnormal y⁻¹ g hg
      rwa [inv_inv] at h1
    have h1 := h.normal i _ hg' _ hm
    have e : y⁻¹ * (g * m * g⁻¹) * y = y⁻¹ * g * y * (y⁻¹ * m * y) * (y⁻¹ * g * y)⁻¹ := by
      group
    rw [e]
    exact h1
  have hMs : IsSimpleGroup ↥(conjSubgroup y (X i)) := by
    have := h.simple i
    exact (Subgroup.equivMapOfInjective (X i) (MulAut.conj y).toMonoidHom
      (MulAut.conj y).injective).symm.isSimpleGroup
  have hMne : conjSubgroup y (X i) ≠ ⊥ := (Subgroup.isSimpleGroup_iff.mp hMs).1
  obtain ⟨j, hj⟩ : ∃ j, conjSubgroup y (X i) ⊓ X j ≠ ⊥ := by
    by_contra hcon
    have hbot : ∀ j', conjSubgroup y (X i) ⊓ X j' = ⊥ := fun j' => by
      by_contra hne
      exact hcon ⟨j', hne⟩
    apply hMne
    rw [Subgroup.eq_bot_iff_forall]
    intro m hm
    have hmG : m ∈ Gs := hMG hm
    have hcomm : ∀ j', ∀ x ∈ X j', m * x = x * m := by
      intro j' x hx
      have hxG : x ∈ Gs := h.le j' hx
      have hc1 : m * x * m⁻¹ * x⁻¹ ∈ X j' :=
        (X j').mul_mem (h.normal j' m hmG x hx) ((X j').inv_mem hx)
      have hc2 : m * x * m⁻¹ * x⁻¹ ∈ conjSubgroup y (X i) := by
        have h3 := (conjSubgroup y (X i)).mul_mem hm
          (hMn x hxG m⁻¹ ((conjSubgroup y (X i)).inv_mem hm))
        have e : m * (x * m⁻¹ * x⁻¹) = m * x * m⁻¹ * x⁻¹ := by group
        rwa [e] at h3
      have hc3 : m * x * m⁻¹ * x⁻¹ ∈ conjSubgroup y (X i) ⊓ X j' := ⟨hc2, hc1⟩
      rw [hbot j', Subgroup.mem_bot] at hc3
      exact mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp hc3)
    have hcen : Gs ≤ Subgroup.centralizer ({m} : Set Y) := by
      rw [← h.gen]
      refine iSup_le fun j' => ?_
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      obtain rfl := Set.mem_singleton_iff.mp hk
      exact hcomm j' x hx
    exact h.centre m hmG fun g hg =>
      Subgroup.mem_centralizer_iff.mp (hcen hg) m (Set.mem_singleton m)
  haveI := h.simple j
  have hXM : X j ≤ conjSubgroup y (X i) :=
    le_of_simple_normalized_inter (conjSubgroup y (X i)) (X j)
      (fun b hb a ha => hMn b (h.le j hb) a ha.1) hj
  have hMX : conjSubgroup y (X i) ≤ X j := by
    refine le_of_simple_normalized_inter (X j) (conjSubgroup y (X i)) ?_ ?_
    · intro b hb a ha
      exact h.normal j b (hMG hb) a ha.1
    · rw [inf_eq_left.mpr hXM]
      exact (Subgroup.isSimpleGroup_iff.mp (h.simple j)).1
  exact ⟨j, le_antisymm hMX hXM⟩

theorem factor_conj {Y : Type} [Group Y] [Finite Y] {ι : Type} [Fintype ι] {Gs : Subgroup Y}
    {X : ι → Subgroup Y} (h : SimpleFactors Gs X) (y : Y) :
    ∃ σ : Equiv.Perm ι, ∀ i, conjSubgroup y (X i) = X (σ i) := by
  have hex : ∀ i, ∃ j, conjSubgroup y (X i) = X j := fun i => factor_conj_exists h y i
  choose f hf using hex
  have hinj : Function.Injective f := by
    intro i i' hii'
    apply h.injective
    apply conjSubgroup_eq_imp_eq y
    rw [hf i, hf i', hii']
  exact ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.mp hinj), fun i => hf i⟩

theorem nonab_simple_not_isPGroup_two {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hnab : ∃ a b : G, a * b ≠ b * a) : ¬ IsPGroup 2 G := by
  intro hP
  have hne : Subgroup.center G ≠ ⊥ := hP.bot_lt_center.ne'
  rcases Subgroup.Normal.eq_bot_or_eq_top (Subgroup.center G) with h1 | h1
  · exact hne h1
  · obtain ⟨a, b, hab⟩ := hnab
    have ha : a ∈ Subgroup.center G := by
      rw [h1]
      exact Subgroup.mem_top a
    exact hab (Subgroup.mem_center_iff.mp ha b).symm

theorem isPGroup_subgroup_of_le {Y : Type} [Group Y] (p : ℕ) {N T : Subgroup Y}
    (hN : IsPGroup p N) (hTN : T ≤ N) : IsPGroup p T := by
  refine isPGroup_iff_pow_pow_eq_one.mpr fun g => ?_
  obtain ⟨k, hk⟩ := (isPGroup_iff_pow_pow_eq_one.mp hN) ⟨(g : Y), hTN g.2⟩
  refine ⟨k, Subtype.ext ?_⟩
  have h1 := congrArg Subtype.val hk
  simpa using h1

theorem no_component {Y : Type} [Group Y] [Finite Y] (Gs K N T : Subgroup Y)
    (hGs : ∀ y : Y, ∀ g ∈ Gs, y * g * y⁻¹ ∈ Gs) (hN2 : IsPGroup 2 N)
    (hNn : ∀ k ∈ K, ∀ n ∈ N, k * n * k⁻¹ ∈ N)
    (hCN : ∀ k ∈ K, (∀ n ∈ N, k * n = n * k) → k ∈ N)
    (hTK : T ≤ K) (hTG : T ≤ Gs) (hTn : ∀ g ∈ Gs, ∀ t ∈ T, g * t * g⁻¹ ∈ T)
    (hTs : IsSimpleGroup ↥T) (hTnab : ∃ a ∈ T, ∃ b ∈ T, a * b ≠ b * a) : False := by
  have hTnot : ¬ IsPGroup 2 ↥T := by
    obtain ⟨a, ha, b, hb, hab⟩ := hTnab
    refine nonab_simple_not_isPGroup_two ⟨⟨a, ha⟩, ⟨b, hb⟩, fun h' => hab ?_⟩
    exact congrArg Subtype.val h'
  have hNT : N ⊓ T = ⊥ := by
    by_contra hne
    exact hTnot (isPGroup_subgroup_of_le 2 hN2
      (le_of_simple_normalized_inter N T (fun b hb a ha => hNn b (hTK hb) a ha.1) hne))
  have hclaim : ∀ n ∈ N, ∀ t ∈ T, n * t = t * n := by
    intro n hn
    obtain ⟨T', hT'⟩ : ∃ T' : Subgroup Y, T' = conjSubgroup n T := ⟨_, rfl⟩
    have hmemT' : ∀ t ∈ T, n * t * n⁻¹ ∈ T' := by
      intro t ht
      rw [hT', mem_conjSubgroup]
      have e : n⁻¹ * (n * t * n⁻¹) * n = t := by group
      rw [e]
      exact ht
    have hT'G : T' ≤ Gs := by
      intro x hx
      rw [hT', mem_conjSubgroup] at hx
      have h1 := hGs n _ (hTG hx)
      have e : n * (n⁻¹ * x * n) * n⁻¹ = x := by group
      rwa [e] at h1
    have hT'n : ∀ g ∈ Gs, ∀ x ∈ T', g * x * g⁻¹ ∈ T' := by
      intro g hg x hx
      rw [hT', mem_conjSubgroup] at hx ⊢
      have hg1 : n⁻¹ * g * n ∈ Gs := by
        have h1 := hGs n⁻¹ g hg
        rwa [inv_inv] at h1
      have h1 := hTn _ hg1 _ hx
      have e : n⁻¹ * g * n * (n⁻¹ * x * n) * (n⁻¹ * g * n)⁻¹
          = n⁻¹ * (g * x * g⁻¹) * n := by
        group
      rwa [e] at h1
    by_cases hne : T' ⊓ T = ⊥
    · exfalso
      have hB : ∀ t ∈ T, ∃ k : ℕ, t ^ 2 ^ k = 1 := by
        intro t ht
        have ht' : n * t * n⁻¹ ∈ T' := hmemT' t ht
        have hcomm : Commute t (n * t * n⁻¹) := by
          have hc1 : t * (n * t * n⁻¹) * t⁻¹ ∈ T' := hT'n t (hTG ht) _ ht'
          have hc2 : t * (n * t * n⁻¹) * t⁻¹ * (n * t * n⁻¹)⁻¹ ∈ T' :=
            T'.mul_mem hc1 (T'.inv_mem ht')
          have hc3 : t * (n * t * n⁻¹) * t⁻¹ * (n * t * n⁻¹)⁻¹ ∈ T := by
            have h1 := hTn _ (hT'G ht') _ (T.inv_mem ht)
            have e : t * (n * t * n⁻¹) * t⁻¹ * (n * t * n⁻¹)⁻¹
                = t * (n * t * n⁻¹ * t⁻¹ * (n * t * n⁻¹)⁻¹) := by
              group
            rw [e]
            exact T.mul_mem ht h1
          have hc4 : t * (n * t * n⁻¹) * t⁻¹ * (n * t * n⁻¹)⁻¹ ∈ T' ⊓ T := ⟨hc2, hc3⟩
          rw [hne, Subgroup.mem_bot] at hc4
          exact mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp hc4)
        have hd : t * n * t⁻¹ * n⁻¹ ∈ N := N.mul_mem (hNn t (hTK ht) n hn) (N.inv_mem hn)
        obtain ⟨k, hk⟩ := hN2 ⟨t * n * t⁻¹ * n⁻¹, hd⟩
        have hk' : (t * n * t⁻¹ * n⁻¹) ^ 2 ^ k = 1 := by
          have h1 := congrArg Subtype.val hk
          simpa using h1
        refine ⟨k, ?_⟩
        have e : t * n * t⁻¹ * n⁻¹ = t * (n * t * n⁻¹)⁻¹ := by group
        rw [e, hcomm.inv_right.mul_pow] at hk'
        have h2 : t ^ 2 ^ k = (n * t * n⁻¹) ^ 2 ^ k := by
          rw [eq_inv_of_mul_eq_one_left hk', inv_pow, inv_inv]
        have hmem : t ^ 2 ^ k ∈ T' ⊓ T :=
          ⟨by rw [h2]; exact T'.pow_mem ht' _, T.pow_mem ht _⟩
        rw [hne, Subgroup.mem_bot] at hmem
        exact hmem
      refine hTnot (isPGroup_iff_pow_pow_eq_one.mpr fun g => ?_)
      obtain ⟨k, hk⟩ := hB (g : Y) g.2
      exact ⟨k, Subtype.ext (by simpa using hk)⟩
    · intro t ht
      have hTT' : T ≤ T' :=
        le_of_simple_normalized_inter T' T (fun b hb a ha => hT'n b (hTG hb) a ha.1) hne
      have hinj : Function.Injective (MulAut.conj n).toMonoidHom := (MulAut.conj n).injective
      have hcard : Nat.card T' ≤ Nat.card T := by
        rw [hT']
        exact (Subgroup.card_map_of_injective hinj).le
      have hTT'eq : T = T' := Subgroup.eq_of_le_of_card_ge hTT' hcard
      have hnt : n * t * n⁻¹ ∈ T := by
        have h1 := hmemT' t ht
        rw [← hTT'eq] at h1
        exact h1
      have hc1 : n * t * n⁻¹ * t⁻¹ ∈ T := T.mul_mem hnt (T.inv_mem ht)
      have hc2 : n * t * n⁻¹ * t⁻¹ ∈ N := by
        have h1 := N.mul_mem hn (hNn t (hTK ht) n⁻¹ (N.inv_mem hn))
        have e : n * (t * n⁻¹ * t⁻¹) = n * t * n⁻¹ * t⁻¹ := by group
        rwa [e] at h1
      have hc3 : n * t * n⁻¹ * t⁻¹ ∈ N ⊓ T := ⟨hc2, hc1⟩
      rw [hNT, Subgroup.mem_bot] at hc3
      exact mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp hc3)
  have hTN : T ≤ N := by
    intro t ht
    refine hCN t (hTK ht) fun n hn => ?_
    exact (hclaim n hn t ht).symm
  exact hTnot (isPGroup_subgroup_of_le 2 hN2 hTN)

theorem proj_conj {Y : Type} [Group Y] [Finite Y] {ι : Type} [Fintype ι] {Gs : Subgroup Y}
    {X : ι → Subgroup Y} (h : SimpleFactors Gs X) {π : ι → ↥Gs →* Y} (hπ : IsProj Gs X π)
    (y : Y) (σ : ι → ι) (hσ : ∀ i, conjSubgroup y (X i) = X (σ i)) (i : ι) (g : ↥Gs) :
    π (σ i) ⟨y * g * y⁻¹, h.gnormal y g g.2⟩ = y * π i g * y⁻¹ := by
  have hmem : ∀ j (x : Y), x ∈ X j → y * x * y⁻¹ ∈ X (σ j) := by
    intro j x hx
    rw [← hσ j, mem_conjSubgroup, show y⁻¹ * (y * x * y⁻¹) * y = x by group]
    exact hx
  have key : ∀ x : Y, x ∈ (⨆ j, X j) → ∃ hx : x ∈ Gs,
      π (σ i) ⟨y * x * y⁻¹, h.gnormal y x hx⟩ = y * π i ⟨x, hx⟩ * y⁻¹ := by
    intro x hx
    refine Subgroup.iSup_induction X (C := fun t => ∃ ht : t ∈ Gs,
      π (σ i) ⟨y * t * y⁻¹, h.gnormal y t ht⟩ = y * π i ⟨t, ht⟩ * y⁻¹) hx ?_ ?_ ?_
    · intro j t htj
      by_cases hji : j = i
      · rw [hji] at htj
        have e1 : π (σ i) ⟨y * t * y⁻¹, h.gnormal y t (h.le i htj)⟩ = y * t * y⁻¹ :=
          hπ.self (σ i) ⟨y * t * y⁻¹, h.gnormal y t (h.le i htj)⟩ (hmem i t htj)
        have e2 : π i ⟨t, h.le i htj⟩ = t := hπ.self i ⟨t, h.le i htj⟩ htj
        exact ⟨h.le i htj, by rw [e1, e2]⟩
      · have hσne : σ i ≠ σ j := by
          intro heq
          have hXX : X j = X i := by
            ext z
            have hz := Subgroup.ext_iff.mp
              (show conjSubgroup y (X j) = conjSubgroup y (X i) by rw [hσ j, hσ i, heq])
              (y * z * y⁻¹)
            rw [mem_conjSubgroup, mem_conjSubgroup,
              show y⁻¹ * (y * z * y⁻¹) * y = z by group] at hz
            exact hz
          exact hji (h.injective hXX)
        have e1 : π (σ i) ⟨y * t * y⁻¹, h.gnormal y t (h.le j htj)⟩ = 1 :=
          hπ.other (σ i) (σ j) hσne ⟨y * t * y⁻¹, h.gnormal y t (h.le j htj)⟩ (hmem j t htj)
        have e2 : π i ⟨t, h.le j htj⟩ = 1 := hπ.other i j (Ne.symm hji) ⟨t, h.le j htj⟩ htj
        exact ⟨h.le j htj, by rw [e1, e2]; simp⟩
    · refine ⟨Gs.one_mem, ?_⟩
      have e1 : (⟨y * 1 * y⁻¹, h.gnormal y 1 Gs.one_mem⟩ : ↥Gs) = 1 :=
        Subtype.ext (by simp)
      have e2 : (⟨1, Gs.one_mem⟩ : ↥Gs) = 1 := Subtype.ext rfl
      rw [e1, e2, map_one, map_one]
      simp
    · rintro t s ⟨ht, et⟩ ⟨hs, es⟩
      have e1 : (⟨y * (t * s) * y⁻¹, h.gnormal y (t * s) (Gs.mul_mem ht hs)⟩ : ↥Gs) =
          ⟨y * t * y⁻¹, h.gnormal y t ht⟩ * ⟨y * s * y⁻¹, h.gnormal y s hs⟩ :=
        Subtype.ext (show y * (t * s) * y⁻¹ = y * t * y⁻¹ * (y * s * y⁻¹) by group)
      have e2 : (⟨t * s, Gs.mul_mem ht hs⟩ : ↥Gs) = ⟨t, ht⟩ * ⟨s, hs⟩ := Subtype.ext rfl
      refine ⟨Gs.mul_mem ht hs, ?_⟩
      rw [e1, e2, map_mul, map_mul, et, es]
      group
  obtain ⟨_, hk⟩ := key g.1 (by rw [h.gen]; exact g.2)
  exact hk

theorem proj_injOn_of_ne {Y : Type} [Group Y] [Finite Y] {ι : Type} [Fintype ι]
    {Gs : Subgroup Y} {X : ι → Subgroup Y} (h : SimpleFactors Gs X) {π : ι → ↥Gs →* Y}
    (hπ : IsProj Gs X π) (V : Subgroup Y) (hVG : V ≤ Gs) (hV2 : ∀ v ∈ V, v * v = 1)
    (hti : IsTI V) (i : ι) (hne : ∃ v : ↥Gs, (v : Y) ∈ V ∧ π i v ≠ 1) :
    ∀ v : ↥Gs, (v : Y) ∈ V → π i v = 1 → v = 1 := by
  intro v0 hv0 hπv0
  by_contra hv01
  obtain ⟨Vi, hVi⟩ : ∃ W : Subgroup Y, W = (V.subgroupOf Gs).map (π i) := ⟨_, rfl⟩
  have memVi : ∀ x : Y, x ∈ Vi ↔ ∃ w : ↥Gs, (w : Y) ∈ V ∧ π i w = x := by
    intro x
    rw [hVi, Subgroup.mem_map]
    simp only [Subgroup.mem_subgroupOf]
  have hsq : ∀ x ∈ Vi, x * x = 1 := by
    intro x hx
    obtain ⟨w, hw, rfl⟩ := (memVi _).1 hx
    have hww : w * w = 1 := Subtype.ext (hV2 _ hw)
    rw [← map_mul, hww, map_one]
  have hconjVi : ∀ a : Y, a ∈ X i → (∀ y ∈ V, a * y * a⁻¹ ∈ V) →
      ∀ x ∈ Vi, a * x * a⁻¹ ∈ Vi := by
    intro a ha hV x hx
    obtain ⟨w, hw, rfl⟩ := (memVi _).1 hx
    have hwV : a * (w : Y) * a⁻¹ ∈ V := hV _ hw
    have hA : π i ⟨a, h.le i ha⟩ = a := hπ.self i ⟨a, h.le i ha⟩ ha
    have e : π i (⟨a, h.le i ha⟩ * w * (⟨a, h.le i ha⟩)⁻¹) = a * π i w * a⁻¹ := by
      rw [map_mul, map_mul, map_inv, hA]
    refine (memVi _).2 ⟨⟨a, h.le i ha⟩ * w * (⟨a, h.le i ha⟩)⁻¹, ?_, e⟩
    exact hwV
  obtain ⟨g, hg, hgVi⟩ : ∃ g ∈ X i, conjSubgroup g Vi ≠ Vi := by
    by_contra hc
    push Not at hc
    have hinv : ∀ a ∈ X i, ∀ x ∈ Vi, a * x * a⁻¹ ∈ Vi := by
      intro a ha x hx
      have hx' : x ∈ conjSubgroup a⁻¹ Vi := by
        rw [hc a⁻¹ (inv_mem ha)]
        exact hx
      rw [mem_conjSubgroup, inv_inv] at hx'
      exact hx'
    have hNn : (Vi.subgroupOf (X i)).Normal := by
      constructor
      intro n hn a
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      exact hinv (a : Y) a.2 _ hn
    have hsimp : IsSimpleGroup ↥(X i) := h.simple i
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Vi.subgroupOf (X i)) with hN | hN
    · obtain ⟨w0, hw0V, hw0⟩ := hne
      have ha0 : (⟨π i w0, hπ.mem i w0⟩ : ↥(X i)) ∈ Vi.subgroupOf (X i) :=
        Subgroup.mem_subgroupOf.mpr ((memVi _).2 ⟨w0, hw0V, rfl⟩)
      rw [hN, Subgroup.mem_bot] at ha0
      exact hw0 (congrArg Subtype.val ha0)
    · have hall : ∀ a ∈ X i, a ∈ Vi := by
        intro a ha
        have hmem2 : (⟨a, ha⟩ : ↥(X i)) ∈ Vi.subgroupOf (X i) := by
          rw [hN]
          exact Subgroup.mem_top _
        exact Subgroup.mem_subgroupOf.mp hmem2
      have hsqX : ∀ a ∈ X i, a * a = 1 := fun a ha => hsq a (hall a ha)
      obtain ⟨a, ha, b, hb, hab⟩ := h.nonab i
      apply hab
      have e1 := inv_eq_of_mul_eq_one_right (hsqX a ha)
      have e2 := inv_eq_of_mul_eq_one_right (hsqX b hb)
      have e3 := inv_eq_of_mul_eq_one_right (hsqX (a * b) ((X i).mul_mem ha hb))
      rw [mul_inv_rev, e1, e2] at e3
      exact e3.symm
  have hGi : π i ⟨g, h.le i hg⟩ = g := hπ.self i ⟨g, h.le i hg⟩ hg
  have hGv : (⟨g, h.le i hg⟩ : ↥Gs) * v0 * (⟨g, h.le i hg⟩)⁻¹ = v0 := by
    apply hπ.inj
    intro j
    by_cases hji : j = i
    · rw [hji, map_mul, map_mul, map_inv, hGi, hπv0]
      simp
    · have hGj : π j ⟨g, h.le i hg⟩ = 1 := hπ.other j i hji ⟨g, h.le i hg⟩ hg
      rw [map_mul, map_mul, map_inv, hGj]
      simp
  have hgv : g * (v0 : Y) * g⁻¹ = v0 := congrArg Subtype.val hGv
  have hcomm : g * (v0 : Y) = (v0 : Y) * g := by
    have e : g * (v0 : Y) = (g * (v0 : Y) * g⁻¹) * g := by group
    rw [hgv] at e
    exact e
  have hinv2 : g⁻¹ * (v0 : Y) * g = v0 := by
    rw [mul_assoc, ← hcomm, inv_mul_cancel_left]
  have hvconj : (v0 : Y) ∈ conjSubgroup g V := by
    rw [mem_conjSubgroup, hinv2]
    exact hv0
  have hne_bot : V ⊓ conjSubgroup g V ≠ ⊥ := by
    intro hbot
    have hmem' : (v0 : Y) ∈ V ⊓ conjSubgroup g V := Subgroup.mem_inf.mpr ⟨hv0, hvconj⟩
    rw [hbot, Subgroup.mem_bot] at hmem'
    exact hv01 (Subtype.ext hmem')
  have hVeq : conjSubgroup g V = V := by
    rcases hti g with hb | hb
    · exact absurd hb hne_bot
    · have hVle : V ≤ conjSubgroup g V := by
        intro x hx
        have hx' : x ∈ V ⊓ conjSubgroup g V := by
          rw [hb]
          exact hx
        exact (Subgroup.mem_inf.mp hx').2
      have hcard : Nat.card (conjSubgroup g V) ≤ Nat.card V :=
        (Subgroup.card_map_of_injective (f := (MulAut.conj g).toMonoidHom) (K := V)
          (MulAut.conj g).injective).le
      exact (Subgroup.eq_of_le_of_card_ge hVle hcard).symm
  have hgV : ∀ y ∈ V, g * y * g⁻¹ ∈ V := by
    intro y hy
    have hy' : g * y * g⁻¹ ∈ conjSubgroup g V := by
      rw [mem_conjSubgroup, show g⁻¹ * (g * y * g⁻¹) * g = y by group]
      exact hy
    rw [hVeq] at hy'
    exact hy'
  have hgV' : ∀ y ∈ V, g⁻¹ * y * g⁻¹⁻¹ ∈ V := by
    intro y hy
    rw [inv_inv]
    have hy' : y ∈ conjSubgroup g V := by
      rw [hVeq]
      exact hy
    exact mem_conjSubgroup.mp hy'
  apply hgVi
  ext x
  rw [mem_conjSubgroup]
  constructor
  · intro hx
    have hx2 := hconjVi g hg hgV _ hx
    rwa [show g * (g⁻¹ * x * g) * g⁻¹ = x by group] at hx2
  · intro hx
    have hx2 := hconjVi g⁻¹ (inv_mem hg) hgV' x hx
    rwa [inv_inv] at hx2

theorem card_le_nine {Y : Type} [Group Y] [Finite Y] {ι : Type} [Fintype ι] {Gs : Subgroup Y}
    {X : ι → Subgroup Y} (h : SimpleFactors Gs X) {π : ι → ↥Gs →* Y} (hπ : IsProj Gs X π)
    (V N K : Subgroup Y) (hVG : V ≤ Gs) (hV2 : ∀ v ∈ V, v * v = 1)
    (hinj : ∀ i, ∀ v : ↥Gs, (v : Y) ∈ V → π i v = 1 → v = 1)
    (hKV : ∀ k ∈ K, conjSubgroup k V = V) (hVK : ∀ g ∈ Subgroup.normalizer (V : Set Y), g ∈ K)
    (hpc : ∀ P : Subgroup Y, P ≤ K → (∀ k ∈ K, conjSubgroup k P = P) → IsPGroup 2 P → P ≤ N)
    (q : ℕ) (hq : 2 ≤ q) (hVcard : Nat.card V = q) (hNcard : Nat.card N = q ^ 9) :
    Fintype.card ι ≤ 9 := by
  obtain ⟨Vi, hVi⟩ : ∃ Vi : ι → Subgroup Y,
      ∀ i (y : Y), y ∈ Vi i ↔ ∃ v : ↥Gs, (v : Y) ∈ V ∧ π i v = y :=
    ⟨fun i => (V.subgroupOf Gs).map (π i), fun i y => by
      simp [Subgroup.mem_map, Subgroup.mem_subgroupOf]⟩
  have hViX : ∀ i, ∀ y ∈ Vi i, y ∈ X i := by
    intro i y hy
    obtain ⟨v, -, rfl⟩ := (hVi i y).1 hy
    exact hπ.mem i v
  have hViCard : ∀ i, Nat.card (Vi i) = q := by
    intro i
    let f : ↥(V.subgroupOf Gs) →* Y := (π i).comp (V.subgroupOf Gs).subtype
    have hf : Function.Injective f := by
      refine (injective_iff_map_eq_one f).2 fun a ha => ?_
      have ha' : π i (a.1 : ↥Gs) = 1 := ha
      exact Subtype.ext (hinj i _ (Subgroup.mem_subgroupOf.1 a.2) ha')
    have hrange : Vi i = f.range := by
      ext y
      rw [hVi i y, MonoidHom.mem_range]
      constructor
      · rintro ⟨v, hv, rfl⟩
        exact ⟨⟨v, Subgroup.mem_subgroupOf.2 hv⟩, rfl⟩
      · rintro ⟨a, rfl⟩
        exact ⟨a.1, Subgroup.mem_subgroupOf.1 a.2, rfl⟩
    rw [hrange, Nat.card_congr (MonoidHom.ofInjective hf).toEquiv.symm,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVG).toEquiv, hVcard]
  obtain ⟨W, hW⟩ : ∃ W : Subgroup Y,
      ∀ y, y ∈ W ↔ ∃ g : ↥Gs, (g : Y) = y ∧ ∀ i, π i g ∈ Vi i := by
    refine ⟨((⨅ i, (Vi i).comap (π i)) : Subgroup ↥Gs).map Gs.subtype, fun y => ?_⟩
    simp only [Subgroup.mem_map, Subgroup.mem_iInf, Subgroup.mem_comap]
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact ⟨g, rfl, hg⟩
    · rintro ⟨g, rfl, hg⟩
      exact ⟨g, hg, rfl⟩
  have hVW : ∀ v ∈ V, v ∈ W := fun v hv =>
    (hW v).2 ⟨⟨v, hVG hv⟩, rfl, fun i => (hVi i _).2 ⟨⟨v, hVG hv⟩, hv, rfl⟩⟩
  have hsq : ∀ y ∈ W, y * y = 1 := by
    intro y hy
    obtain ⟨g, rfl, hg⟩ := (hW y).1 hy
    have key : g * g = 1 := by
      refine hπ.inj _ _ fun i => ?_
      obtain ⟨v, hvV, hvg⟩ := (hVi i _).1 (hg i)
      have hvv : v * v = 1 := Subtype.ext (by simpa using hV2 _ hvV)
      rw [map_mul, map_one, ← hvg, ← map_mul, hvv, map_one]
    simpa using congrArg Subtype.val key
  have hWp : IsPGroup 2 W := by
    intro g
    refine ⟨1, ?_⟩
    rw [pow_one, pow_two]
    exact Subtype.ext (by simpa using hsq _ g.2)
  have hcomm : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a := by
    intro a ha b hb
    have hab : a * b * (a * b) = 1 := hsq _ (W.mul_mem ha hb)
    have ha2 : a⁻¹ = a := inv_eq_of_mul_eq_one_right (hsq a ha)
    have hb2 : b⁻¹ = b := inv_eq_of_mul_eq_one_right (hsq b hb)
    calc a * b = (a * b)⁻¹ := (inv_eq_of_mul_eq_one_right hab).symm
      _ = b⁻¹ * a⁻¹ := mul_inv_rev a b
      _ = b * a := by rw [ha2, hb2]
  have hWK : W ≤ K := by
    intro g hg
    refine hVK g (Subgroup.mem_normalizer_iff.2 fun x => ?_)
    show x ∈ V ↔ g * x * g⁻¹ ∈ V
    constructor
    · intro hx
      rw [hcomm g hg x (hVW x hx), mul_inv_cancel_right]
      exact hx
    · intro hx
      have hvW : g * x * g⁻¹ ∈ W := hVW _ hx
      have hc : g⁻¹ * (g * x * g⁻¹) = g * x * g⁻¹ * g⁻¹ :=
        hcomm _ (W.inv_mem hg) _ hvW
      have hx' : x = g * x * g⁻¹ := by
        calc x = g⁻¹ * (g * x * g⁻¹) * g := by group
          _ = g * x * g⁻¹ * g⁻¹ * g := by rw [hc]
          _ = g * x * g⁻¹ := by group
      rw [hx']
      exact hx
  have hWconj : ∀ k ∈ K, ∀ x ∈ W, k * x * k⁻¹ ∈ W := by
    intro k hk x hx
    obtain ⟨g, rfl, hg⟩ := (hW x).1 hx
    obtain ⟨σ, hσ⟩ := factor_conj h k
    refine (hW _).2 ⟨⟨k * (g : Y) * k⁻¹, h.gnormal k (g : Y) g.2⟩, rfl, fun j => ?_⟩
    obtain ⟨i, rfl⟩ : ∃ i, σ i = j := ⟨σ.symm j, σ.apply_symm_apply j⟩
    obtain ⟨v, hvV, hvg⟩ := (hVi i _).1 (hg i)
    have hkv : k * (v : Y) * k⁻¹ ∈ V := by
      have hmem : (v : Y) ∈ conjSubgroup k⁻¹ V := by
        rw [hKV k⁻¹ (K.inv_mem hk)]
        exact hvV
      simpa using mem_conjSubgroup.1 hmem
    rw [proj_conj h hπ k σ hσ i g, ← hvg, ← proj_conj h hπ k σ hσ i v]
    exact (hVi (σ i) _).2 ⟨⟨k * (v : Y) * k⁻¹, h.gnormal k (v : Y) v.2⟩, hkv, rfl⟩
  have hWeq : ∀ k ∈ K, conjSubgroup k W = W := by
    intro k hk
    ext y
    rw [mem_conjSubgroup]
    constructor
    · intro hy
      have e : k * (k⁻¹ * y * k) * k⁻¹ = y := by group
      have := hWconj k hk _ hy
      rwa [e] at this
    · intro hy
      have := hWconj k⁻¹ (K.inv_mem hk) y hy
      rwa [inv_inv] at this
  have hWN : W ≤ N := hpc W hWK hWeq hWp
  have hcardW : q ^ Fintype.card ι ≤ Nat.card W := by
    have hlift : ∀ a : ∀ i, ↥(Vi i), ∃ g : ↥Gs, ∀ i, π i g = (a i : Y) :=
      fun a => hπ.surj (fun i => (a i : Y)) fun i => hViX i _ (a i).2
    choose c hc using hlift
    have hcW : ∀ a : ∀ i, ↥(Vi i), (c a : Y) ∈ W := fun a =>
      (hW _).2 ⟨c a, rfl, fun i => by rw [hc a i]; exact (a i).2⟩
    let Φ : (∀ i, ↥(Vi i)) → ↥W := fun a => ⟨(c a : Y), hcW a⟩
    have hΦ : Function.Injective Φ := by
      intro a b hab
      have h2 : ((Φ a : ↥W) : Y) = ((Φ b : ↥W) : Y) := congrArg Subtype.val hab
      have h1 : c a = c b := Subtype.ext h2
      funext i
      apply Subtype.ext
      rw [← hc a i, ← hc b i, h1]
    have hcard : Nat.card (∀ i, ↥(Vi i)) = q ^ Fintype.card ι := by
      rw [Nat.card_pi]
      simp [hViCard, Finset.prod_const, Finset.card_univ]
    rw [← hcard]
    exact Nat.card_le_card_of_injective Φ hΦ
  have hle : q ^ Fintype.card ι ≤ q ^ 9 :=
    calc q ^ Fintype.card ι ≤ Nat.card W := hcardW
      _ ≤ Nat.card N := Subgroup.card_le_of_le hWN
      _ = q ^ 9 := hNcard
  exact (Nat.pow_le_pow_iff_right (show 1 < q by omega)).1 hle

end CFSG.RankThree.GF2n.Stroth80
