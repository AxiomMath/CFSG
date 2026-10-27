module

public import CFSG.RankThree.GF2n.Tim77.Cor2Hyp
public import CFSG.RankThree.GF2n.Stroth80.Sec7TailLieStmts
import all CFSG.Timmesfeld.RootInvolutions.RootInvolutionSetting
public import CFSG.RankThree.GF2n.Stroth80.Sec311Cover

public section

namespace CFSG.RankThree.GF2n.Tim77

open CFSG.CGT.Timmesfeld75 CFSG.Timmesfeld.RootInvolutions CFSG.Open Subgroup
open CFSG.RankThree.GF2n.Stroth80
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem tim77_conj_inv_conj (g : G) (W : Subgroup G) :
    conjSubgroup g⁻¹ (conjSubgroup g W) = W := by
  rw [← CFSG.RankThree.GF2n.conjSubgroup_mul, inv_mul_cancel,
    CFSG.RankThree.GF2n.conjSubgroup_one]

omit [Finite G] in
theorem tim77_conj_conj_inv (g : G) (W : Subgroup G) :
    conjSubgroup g (conjSubgroup g⁻¹ W) = W := by
  rw [← CFSG.RankThree.GF2n.conjSubgroup_mul, mul_inv_cancel,
    CFSG.RankThree.GF2n.conjSubgroup_one]

omit [Finite G] in
theorem tim77_conj_mono (g : G) {X Y : Subgroup G} (h : X ≤ Y) :
    conjSubgroup g X ≤ conjSubgroup g Y :=
  Subgroup.map_mono h

omit [Finite G] in
theorem tim77_conj_bot (g : G) : conjSubgroup g (⊥ : Subgroup G) = ⊥ :=
  Subgroup.map_bot _

omit [Finite G] in
theorem tim77_commutator_conj (g : G) (X Y : Subgroup G) :
    ⁅conjSubgroup g X, conjSubgroup g Y⁆ = conjSubgroup g ⁅X, Y⁆ :=
  (Subgroup.map_commutator X Y (MulAut.conj g).toMonoidHom).symm

omit [Finite G] in
theorem le_centralizer_conj_iff (g : G) (X Y : Subgroup G) :
    conjSubgroup g X ≤ Subgroup.centralizer (conjSubgroup g Y : Set G) ↔
      X ≤ Subgroup.centralizer (Y : Set G) := by
  constructor
  · intro h x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hx' : g * x * g⁻¹ ∈ conjSubgroup g X := by
      rw [mem_conjSubgroup, show g⁻¹ * (g * x * g⁻¹) * g = x by group]
      exact hx
    have hy' : g * y * g⁻¹ ∈ conjSubgroup g Y := by
      rw [mem_conjSubgroup, show g⁻¹ * (g * y * g⁻¹) * g = y by group]
      exact hy
    have hc := Subgroup.mem_centralizer_iff.mp (h hx') (g * y * g⁻¹) hy'
    calc y * x = g⁻¹ * ((g * y * g⁻¹) * (g * x * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * x * g⁻¹) * (g * y * g⁻¹)) * g := by rw [hc]
      _ = x * y := by group
  · intro h x' hx'
    rw [mem_conjSubgroup] at hx'
    rw [Subgroup.mem_centralizer_iff]
    intro y' hy'
    have hy'' : y' ∈ conjSubgroup g Y := hy'
    rw [mem_conjSubgroup] at hy''
    have hc := Subgroup.mem_centralizer_iff.mp (h hx') (g⁻¹ * y' * g) hy''
    calc y' * x' = g * ((g⁻¹ * y' * g) * (g⁻¹ * x' * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * x' * g) * (g⁻¹ * y' * g)) * g⁻¹ := by rw [hc]
      _ = x' * y' := by group

omit [Finite G] in
theorem tim77_mul_comm_of_conj {g a b : G}
    (h : (g⁻¹ * a * g) * (g⁻¹ * b * g) = (g⁻¹ * b * g) * (g⁻¹ * a * g)) : a * b = b * a := by
  calc a * b = g * ((g⁻¹ * a * g) * (g⁻¹ * b * g)) * g⁻¹ := by group
    _ = g * ((g⁻¹ * b * g) * (g⁻¹ * a * g)) * g⁻¹ := by rw [h]
    _ = b * a := by group

omit [Finite G] in
theorem normalizerIn_ne_bot_of_mem {X Y : Subgroup G} {y : G} (hy : y ∈ X)
    (hyN : y ∈ Subgroup.normalizer (Y : Set G)) (hy1 : y ≠ 1) : normalizerIn X Y ≠ ⊥ := by
  intro h
  apply hy1
  have hmem : y ∈ normalizerIn X Y := Subgroup.mem_inf.mpr ⟨hy, hyN⟩
  rw [h] at hmem
  exact Subgroup.mem_bot.mp hmem

omit [Finite G] in
theorem normalizerIn_conj_ne_bot_of (g : G) {X Y : Subgroup G}
    (h : normalizerIn X Y ≠ ⊥) : normalizerIn (conjSubgroup g X) (conjSubgroup g Y) ≠ ⊥ := by
  obtain ⟨⟨z, hz⟩, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp h
  have hzX : z ∈ X := (Subgroup.mem_inf.mp hz).1
  have hzN : z ∈ Subgroup.normalizer (Y : Set G) := (Subgroup.mem_inf.mp hz).2
  have hz1' : z ≠ 1 := by
    intro e
    apply hz1
    exact Subtype.ext e
  have hzY : conjSubgroup z Y = Y := CFSG.RankThree.GF2n.conjSubgroup_eq_self_iff.mpr hzN
  have hN : conjSubgroup (g * z * g⁻¹) (conjSubgroup g Y) = conjSubgroup g Y := by
    rw [← CFSG.RankThree.GF2n.conjSubgroup_mul, show g * z * g⁻¹ * g = g * z by group,
      CFSG.RankThree.GF2n.conjSubgroup_mul, hzY]
  have hmem : g * z * g⁻¹ ∈ normalizerIn (conjSubgroup g X) (conjSubgroup g Y) := by
    refine Subgroup.mem_inf.mpr ⟨?_, CFSG.RankThree.GF2n.conjSubgroup_eq_self_iff.mp hN⟩
    rw [mem_conjSubgroup, show g⁻¹ * (g * z * g⁻¹) * g = z by group]
    exact hzX
  rw [Subgroup.ne_bot_iff_exists_ne_one]
  refine ⟨⟨g * z * g⁻¹, hmem⟩, fun e => hz1' ?_⟩
  have e' : g * z * g⁻¹ = 1 := congrArg Subtype.val e
  calc z = g⁻¹ * (g * z * g⁻¹) * g := by group
    _ = 1 := by rw [e']; group

omit [Finite G] in
theorem normalizerIn_conj_ne_bot_iff (g : G) (X Y : Subgroup G) :
    normalizerIn (conjSubgroup g X) (conjSubgroup g Y) ≠ ⊥ ↔ normalizerIn X Y ≠ ⊥ := by
  constructor
  · intro h
    have h' := normalizerIn_conj_ne_bot_of g⁻¹ h
    rwa [tim77_conj_inv_conj, tim77_conj_inv_conj] at h'
  · exact normalizerIn_conj_ne_bot_of g

omit [Finite G] in
theorem isTI_of_isRootType {A : Subgroup G} (hroot : IsRootType 2 A) : IsTI A := by
  obtain ⟨-, -, hT0, -⟩ := hroot
  exact fun k => (hT0 k (Subgroup.mem_top k)).symm

omit [Finite G] in
theorem isRootType_conj {A : Subgroup G} (hroot : IsRootType 2 A) (g : G) :
    IsRootType 2 (conjSubgroup g A) := by
  obtain ⟨-, hel, hT0, hcomm⟩ := hroot
  have hTI : IsTI A := fun k => (hT0 k (Subgroup.mem_top k)).symm
  refine ⟨le_top, isElemAbelian_conj hel g, fun h _ => ?_, fun h _ hN => ?_⟩
  · exact (CFSG.RankThree.GF2n.isTI_conjSubgroup hTI g h).symm
  · have hEq : conjSubgroup h (conjSubgroup g A) =
        conjSubgroup g (conjSubgroup (g⁻¹ * h * g) A) := by
      rw [← CFSG.RankThree.GF2n.conjSubgroup_mul, ← CFSG.RankThree.GF2n.conjSubgroup_mul,
        show g * (g⁻¹ * h * g) = h * g by group]
    have hN' : normalizerIn A (conjSubgroup (g⁻¹ * h * g) A) ≠ ⊥ :=
      (normalizerIn_conj_ne_bot_iff g A (conjSubgroup (g⁻¹ * h * g) A)).mp
        (by rw [← hEq]; exact hN)
    have hc := hcomm (g⁻¹ * h * g) (Subgroup.mem_top _) hN'
    intro a' ha' b' hb'
    rw [mem_conjSubgroup] at ha'
    rw [hEq, mem_conjSubgroup] at hb'
    exact tim77_mul_comm_of_conj (hc _ ha' _ hb')

omit [Finite G] in
theorem WAC_le_of_gen (A Z : Subgroup G)
    (h : ∀ g : G, conjSubgroup g A ≤ Subgroup.centralizer (A : Set G) → conjSubgroup g A ≤ Z) :
    WAC A ≤ Z := by
  unfold WAC
  exact iSup₂_le fun g hg => h g hg

omit [Finite G] in
theorem WAC_le_centralizer (A : Subgroup G) : WAC A ≤ Subgroup.centralizer (A : Set G) :=
  WAC_le_of_gen A _ fun _ hg => hg

omit [Finite G] in
theorem conj_le_WAC {A : Subgroup G} {g : G}
    (hg : conjSubgroup g A ≤ Subgroup.centralizer (A : Set G)) : conjSubgroup g A ≤ WAC A := by
  unfold WAC
  exact le_iSup₂_of_le g hg le_rfl

omit [Finite G] in
theorem wac_conj_le (A : Subgroup G) (g : G) :
    WAC (conjSubgroup g A) ≤ conjSubgroup g (WAC A) := by
  refine WAC_le_of_gen (conjSubgroup g A) _ fun h hh => ?_
  have e : conjSubgroup g (conjSubgroup (g⁻¹ * h * g) A) = conjSubgroup h (conjSubgroup g A) := by
    rw [← CFSG.RankThree.GF2n.conjSubgroup_mul, ← CFSG.RankThree.GF2n.conjSubgroup_mul,
      show g * (g⁻¹ * h * g) = h * g by group]
  have hm : conjSubgroup (g⁻¹ * h * g) A ≤ Subgroup.centralizer (A : Set G) :=
    (le_centralizer_conj_iff g _ _).mp (by rw [e]; exact hh)
  rw [← e]
  exact tim77_conj_mono g (conj_le_WAC hm)

theorem wac_conj (A : Subgroup G) (g : G) : WAC (conjSubgroup g A) = conjSubgroup g (WAC A) := by
  refine le_antisymm (wac_conj_le A g) ?_
  have h2 : WAC A ≤ conjSubgroup g⁻¹ (WAC (conjSubgroup g A)) := by
    have h := wac_conj_le (conjSubgroup g A) g⁻¹
    rwa [tim77_conj_inv_conj] at h
  calc conjSubgroup g (WAC A) ≤ conjSubgroup g (conjSubgroup g⁻¹ (WAC (conjSubgroup g A))) :=
        tim77_conj_mono g h2
    _ = WAC (conjSubgroup g A) := tim77_conj_conj_inv g _

theorem commute_of_mem_conj {A : Subgroup G} (hroot : IsRootType 2 A) {g h x y : G}
    (hx : x ∈ conjSubgroup g A) (hx1 : x ≠ 1) (hy : y ∈ conjSubgroup h A) (hy1 : y ≠ 1)
    (hxy : x * y = y * x) :
    ∀ a ∈ conjSubgroup g A, ∀ b ∈ conjSubgroup h A, a * b = b * a := by
  have hTI : IsTI A := isTI_of_isRootType hroot
  have hyN : y ∈ Subgroup.normalizer ((conjSubgroup g A : Subgroup G) : Set G) :=
    mem_normalizer_of_commute_of_isTI (CFSG.RankThree.GF2n.isTI_conjSubgroup hTI g) hx hx1
      hxy.symm
  have hne : normalizerIn (conjSubgroup h A) (conjSubgroup g A) ≠ ⊥ :=
    normalizerIn_ne_bot_of_mem hy hyN hy1
  have hk : conjSubgroup (g * h⁻¹) (conjSubgroup h A) = conjSubgroup g A := by
    rw [← CFSG.RankThree.GF2n.conjSubgroup_mul, inv_mul_cancel_right]
  obtain ⟨-, -, -, hcomm0⟩ := isRootType_conj hroot h
  have hcomm : ∀ a' ∈ conjSubgroup h A, ∀ b' ∈ conjSubgroup (g * h⁻¹) (conjSubgroup h A),
      a' * b' = b' * a' :=
    hcomm0 (g * h⁻¹) (Subgroup.mem_top _) (by rw [hk]; exact hne)
  rw [hk] at hcomm
  intro a ha b hb
  exact (hcomm b hb a ha).symm

omit [Finite G] in
theorem tim77_commutator_mul_left {x x' y : G} (h : x * ⁅x', y⁆ = ⁅x', y⁆ * x) :
    ⁅x * x', y⁆ = ⁅x', y⁆ * ⁅x, y⁆ := by
  simp only [commutatorElement_def] at h ⊢
  calc x * x' * y * (x * x')⁻¹ * y⁻¹
      = x * (x' * y * x'⁻¹ * y⁻¹) * x⁻¹ * (x * y * x⁻¹ * y⁻¹) := by group
    _ = (x' * y * x'⁻¹ * y⁻¹) * x * x⁻¹ * (x * y * x⁻¹ * y⁻¹) := by rw [h]
    _ = (x' * y * x'⁻¹ * y⁻¹) * (x * y * x⁻¹ * y⁻¹) := by group

omit [Finite G] in
theorem tim77_commutator_mul_right {a b c : G} (h : b * ⁅a, c⁆ = ⁅a, c⁆ * b) :
    ⁅a, b * c⁆ = ⁅a, b⁆ * ⁅a, c⁆ := by
  simp only [commutatorElement_def] at h ⊢
  have hbU : b * (a * c * a⁻¹ * c⁻¹) * b⁻¹ = a * c * a⁻¹ * c⁻¹ := by
    rw [h]
    group
  calc a * (b * c) * a⁻¹ * (b * c)⁻¹
      = (a * b * a⁻¹ * b⁻¹) * (b * (a * c * a⁻¹ * c⁻¹) * b⁻¹) := by group
    _ = (a * b * a⁻¹ * b⁻¹) * (a * c * a⁻¹ * c⁻¹) := by rw [hbU]

theorem commutator_wac_eq {A : Subgroup G} (hA : IsElemAbelian 2 A) (hTI : IsTI A)
    (hroot : IsRootType 2 A) (hW : ⁅WAC A, WAC A⁆ ≤ A) (hne : ⁅WAC A, WAC A⁆ ≠ ⊥) :
    ⁅WAC A, WAC A⁆ = A := by
  obtain ⟨g, h, hg, hh, a, ha, b, hb, hab⟩ : ∃ g h : G,
      conjSubgroup g A ≤ Subgroup.centralizer (A : Set G) ∧
        conjSubgroup h A ≤ Subgroup.centralizer (A : Set G) ∧
        ∃ a ∈ conjSubgroup g A, ∃ b ∈ conjSubgroup h A, a * b ≠ b * a := by
    by_contra hcon
    apply hne
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    refine WAC_le_of_gen A _ fun g hg => ?_
    rw [Subgroup.le_centralizer_iff]
    refine WAC_le_of_gen A _ fun h hh => ?_
    rw [Subgroup.le_centralizer_iff]
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    by_contra hxy
    exact hcon ⟨g, h, hg, hh, x, hx, y, hy, fun e => hxy e.symm⟩
  have hb1 : b ≠ 1 := by
    rintro rfl
    exact hab (by simp)
  have hxb : ∀ x ∈ conjSubgroup g A, x ≠ 1 → x * b ≠ b * x := fun x hx hx1 e =>
    hab (commute_of_mem_conj hroot hx hx1 hb hb1 e a ha b hb)
  have hgW : conjSubgroup g A ≤ WAC A := conj_le_WAC hg
  have hbW : b ∈ WAC A := conj_le_WAC hh hb
  have hWc : ∀ w ∈ WAC A, ∀ c ∈ A, c * w = w * c := fun w hw c hc =>
    Subgroup.mem_centralizer_iff.mp (WAC_le_centralizer A hw) c hc
  have hAcomm : ∀ u ∈ A, ∀ v ∈ A, u * v = v * u := fun u hu v hv =>
    congrArg Subtype.val (hA.1.is_comm.comm ⟨u, hu⟩ ⟨v, hv⟩)
  have hcomm_mem : ∀ x ∈ conjSubgroup g A, ⁅x, b⁆ ∈ A := fun x hx =>
    hW (Subgroup.commutator_mem_commutator (hgW hx) hbW)
  let φ : conjSubgroup g A →* ↥(⁅WAC A, WAC A⁆) := MonoidHom.mk'
    (fun x => ⟨⁅(x : G), b⁆, Subgroup.commutator_mem_commutator (hgW x.2) hbW⟩) (by
      intro x x'
      apply Subtype.ext
      show ⁅(x : G) * (x' : G), b⁆ = ⁅(x : G), b⁆ * ⁅(x' : G), b⁆
      rw [tim77_commutator_mul_left ((hWc _ (hgW x.2) _ (hcomm_mem _ x'.2)).symm)]
      exact hAcomm _ (hcomm_mem _ x'.2) _ (hcomm_mem _ x.2))
  have hφinj : Function.Injective φ := by
    refine (injective_iff_map_eq_one φ).2 fun x hx => ?_
    have h1 : ⁅(x : G), b⁆ = 1 := congrArg Subtype.val hx
    have h2 : (x : G) * b = b * (x : G) := commutatorElement_eq_one_iff_mul_comm.mp h1
    by_contra hxne
    exact hxb (x : G) x.2 (fun e => hxne (Subtype.ext e)) h2
  have hcard : Nat.card A ≤ Nat.card ↥(⁅WAC A, WAC A⁆) := by
    rw [← CFSG.RankThree.GF2n.card_conjSubgroup g A]
    exact Nat.card_le_card_of_injective φ hφinj
  exact Subgroup.eq_of_le_of_card_ge hW hcard

theorem isConj_core {A : Subgroup G} (hA : IsElemAbelian 2 A) (hTI : IsTI A)
    (hroot : IsRootType 2 A) (hW : ⁅WAC A, WAC A⁆ ≤ A) (hne : ⁅WAC A, WAC A⁆ ≠ ⊥)
    {g τ : G} (hk : conjSubgroup g A ≤ Subgroup.centralizer (A : Set G))
    (hτ : τ ∈ conjSubgroup g A) (hτA : τ ∉ A) :
    ∀ b ∈ A, IsConj τ (τ * b) := by
  have hWd : ⁅WAC A, WAC A⁆ = A := commutator_wac_eq hA hTI hroot hW hne
  have hτ1 : τ ≠ 1 := by
    intro e
    apply hτA
    rw [e]
    exact A.one_mem
  have hτ2 : τ * τ = 1 := by
    rw [← sq]
    exact (isElemAbelian_conj hA g).2 τ hτ
  have hτinv : τ⁻¹ = τ := inv_eq_of_mul_eq_one_right hτ2
  have hWc : ∀ w ∈ WAC A, ∀ c ∈ A, c * w = w * c := fun w hw c hc =>
    Subgroup.mem_centralizer_iff.mp (WAC_le_centralizer A hw) c hc
  have hτW : τ ∈ WAC A := conj_le_WAC hk hτ
  obtain ⟨m, hm, x0, hx0, hx0τ⟩ : ∃ m : G, conjSubgroup m A ≤ Subgroup.centralizer (A : Set G) ∧
      ∃ x ∈ conjSubgroup m A, x * τ ≠ τ * x := by
    by_contra hcon
    have hcon' : ∀ m : G, conjSubgroup m A ≤ Subgroup.centralizer (A : Set G) →
        ∀ x ∈ conjSubgroup m A, x * τ = τ * x := fun m hm x hx => by
      by_contra e
      exact hcon ⟨m, hm, x, hx, e⟩
    have hWτ : WAC A ≤ Subgroup.centralizer ({τ} : Set G) := by
      refine WAC_le_of_gen A _ fun m hm => ?_
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro t ht
      rw [Set.mem_singleton_iff.mp ht]
      exact (hcon' m hm x hx).symm
    have hWτ' : ∀ w ∈ WAC A, τ * w = w * τ := fun w hw =>
      Subgroup.mem_centralizer_iff.mp (hWτ hw) τ (Set.mem_singleton τ)
    have hWN : ∀ w ∈ WAC A, w ∈ Subgroup.normalizer ((conjSubgroup g A : Subgroup G) : Set G) :=
      fun w hw => mem_normalizer_of_commute_of_isTI
        (CFSG.RankThree.GF2n.isTI_conjSubgroup hTI g) hτ hτ1 (hWτ' w hw).symm
    have hgen : ∀ m : G, conjSubgroup m A ≤ Subgroup.centralizer (A : Set G) →
        conjSubgroup m A ≤ Subgroup.centralizer ((conjSubgroup g A : Subgroup G) : Set G) := by
      intro m hm x hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      by_cases hx1 : x = 1
      · rw [hx1, mul_one, one_mul]
      · have hxN := hWN x (conj_le_WAC hm hx)
        have hne' : normalizerIn (conjSubgroup m A) (conjSubgroup g A) ≠ ⊥ :=
          normalizerIn_ne_bot_of_mem hx hxN hx1
        obtain ⟨-, -, -, hcm⟩ := isRootType_conj hroot m
        have hmg : conjSubgroup (g * m⁻¹) (conjSubgroup m A) = conjSubgroup g A := by
          rw [← CFSG.RankThree.GF2n.conjSubgroup_mul, inv_mul_cancel_right]
        have hc := hcm (g * m⁻¹) (Subgroup.mem_top _) (by rw [hmg]; exact hne')
        rw [hmg] at hc
        exact (hc x hx y hy).symm
    have hWle : WAC A ≤ WAC (conjSubgroup g A) := by
      refine WAC_le_of_gen A _ fun m hm => ?_
      have hmg' : conjSubgroup (m * g⁻¹) (conjSubgroup g A) = conjSubgroup m A := by
        rw [← CFSG.RankThree.GF2n.conjSubgroup_mul, inv_mul_cancel_right]
      have hc : conjSubgroup (m * g⁻¹) (conjSubgroup g A) ≤
          Subgroup.centralizer ((conjSubgroup g A : Subgroup G) : Set G) := by
        rw [hmg']
        exact hgen m hm
      rw [← hmg']
      exact conj_le_WAC hc
    have hcomm_g : ⁅WAC (conjSubgroup g A), WAC (conjSubgroup g A)⁆ = conjSubgroup g A := by
      rw [wac_conj, tim77_commutator_conj, hWd]
    have hAle : A ≤ conjSubgroup g A :=
      calc A = ⁅WAC A, WAC A⁆ := hWd.symm
        _ ≤ ⁅WAC (conjSubgroup g A), WAC (conjSubgroup g A)⁆ :=
          Subgroup.commutator_mono hWle hWle
        _ = conjSubgroup g A := hcomm_g
    have hAeq : A = conjSubgroup g A :=
      Subgroup.eq_of_le_of_card_ge hAle (le_of_eq (CFSG.RankThree.GF2n.card_conjSubgroup g A))
    exact hτA (by rw [hAeq]; exact hτ)
  have hmW : ∀ x ∈ conjSubgroup m A, x ∈ WAC A := fun x hx => conj_le_WAC hm hx
  have hτx : ∀ x ∈ conjSubgroup m A, ⁅τ, x⁆ ∈ A := fun x hx =>
    hW (Subgroup.commutator_mem_commutator hτW (hmW x hx))
  let φ : conjSubgroup m A →* A := MonoidHom.mk'
    (fun x => ⟨⁅τ, (x : G)⁆, hτx (x : G) x.2⟩) (by
      intro x x'
      apply Subtype.ext
      show ⁅τ, (x : G) * (x' : G)⁆ = ⁅τ, (x : G)⁆ * ⁅τ, (x' : G)⁆
      rw [tim77_commutator_mul_right ((hWc _ (hmW _ x.2) _ (hτx _ x'.2)).symm)])
  have hφinj : Function.Injective φ := by
    refine (injective_iff_map_eq_one φ).2 fun x hx => ?_
    have h1 : ⁅τ, (x : G)⁆ = 1 := congrArg Subtype.val hx
    have h2 : τ * (x : G) = (x : G) * τ := commutatorElement_eq_one_iff_mul_comm.mp h1
    by_contra hxne
    have hx1G : (x : G) ≠ 1 := fun e => hxne (Subtype.ext e)
    exact hx0τ (commute_of_mem_conj hroot x.2 hx1G hτ hτ1 h2.symm x0 hx0 τ hτ)
  have hφbij : Function.Bijective φ :=
    hφinj.bijective_of_nat_card_le (le_of_eq (CFSG.RankThree.GF2n.card_conjSubgroup m A).symm)
  intro b hb
  obtain ⟨x, hx⟩ := hφbij.2 ⟨b, hb⟩
  have hxb : ⁅τ, (x : G)⁆ = b := congrArg Subtype.val hx
  rw [← hxb, isConj_iff]
  refine ⟨(x : G), ?_⟩
  rw [commutatorElement_def]
  calc (x : G) * τ * (x : G)⁻¹ = (x : G) * τ⁻¹ * (x : G)⁻¹ := by rw [hτinv]
    _ = (τ * τ) * (x : G) * τ⁻¹ * (x : G)⁻¹ := by rw [hτ2, one_mul]
    _ = τ * (τ * (x : G) * τ⁻¹ * (x : G)⁻¹) := by group

theorem isConj_mul_of_not_mem {A : Subgroup G} (hA : IsElemAbelian 2 A) (hTI : IsTI A)
    (hroot : IsRootType 2 A) (hW : ⁅WAC A, WAC A⁆ ≤ A) (hne : ⁅WAC A, WAC A⁆ ≠ ⊥)
    {g k τ : G} (hk : conjSubgroup g A ≤ centralizer (conjSubgroup k A : Set G))
    (hτ : τ ∈ conjSubgroup g A) (hτk : τ ∉ conjSubgroup k A) :
    ∀ b ∈ conjSubgroup k A, IsConj τ (τ * b) := by
  have hA' := isElemAbelian_conj hA k
  have hTI' := CFSG.RankThree.GF2n.isTI_conjSubgroup hTI k
  have hroot' := isRootType_conj hroot k
  have hW' : ⁅WAC (conjSubgroup k A), WAC (conjSubgroup k A)⁆ ≤ conjSubgroup k A := by
    rw [wac_conj, tim77_commutator_conj]
    exact tim77_conj_mono k hW
  have hne' : ⁅WAC (conjSubgroup k A), WAC (conjSubgroup k A)⁆ ≠ ⊥ := by
    rw [wac_conj, tim77_commutator_conj]
    intro h0
    apply hne
    have e := tim77_conj_inv_conj k ⁅WAC A, WAC A⁆
    rw [h0, tim77_conj_bot] at e
    exact e.symm
  have hk' : conjSubgroup (g * k⁻¹) (conjSubgroup k A) ≤
      Subgroup.centralizer ((conjSubgroup k A : Subgroup G) : Set G) := by
    rw [← CFSG.RankThree.GF2n.conjSubgroup_mul, inv_mul_cancel_right]
    exact hk
  have hτ' : τ ∈ conjSubgroup (g * k⁻¹) (conjSubgroup k A) := by
    rw [← CFSG.RankThree.GF2n.conjSubgroup_mul, inv_mul_cancel_right]
    exact hτ
  exact isConj_core hA' hTI' hroot' hW' hne' hk' hτ' hτk

end CFSG.RankThree.GF2n.Tim77
