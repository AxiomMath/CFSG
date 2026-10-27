module

public import CFSG.Quasithin.Background.E6Eighteen
import CFSG.GroupTheory.Fitting.LayerTopBot
public import CFSG.CharacterTheory.Semidihedral.CentralizerAlternatives
public import CFSG.Quasithin.Background.E6TwentyTwo

public section

namespace CFSG.Quasithin

namespace E6

open CFSG.Open CFSG.QuasithinUnique

@[expose] def E619Insp : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (K R D : Subgroup Y) (z u : Y),
    CFSG.IsQuasisimple ↥K → Lemma115Cases K z → IsPGroup 2 R →
    R ≤ Subgroup.normalizer (K : Set Y) → IsSylowTwoOf (R ⊓ K) K →
    z ∈ R → z ∈ Subgroup.centralizer (R : Set Y) → z ^ 2 = 1 →
    u ∈ R → u ∈ Subgroup.centralizer (R : Set Y) → u ^ 2 = 1 →
    u ∉ Subgroup.centralizer (K : Set Y) →
    Odd (Nat.card D) → D ≤ Subgroup.normalizer (K : Set Y) →
    D ≤ Subgroup.centralizer ({u} : Set Y) → (∀ d ∈ D, z⁻¹ * d * z = d⁻¹) →
    ¬ D ≤ Subgroup.centralizer (K : Set Y) → IsA7Type K

section Tools

variable {G : Type} [Group G] [Finite G]

theorem le_centralizer_of_AxB {X P A D : Subgroup G} (hP : IsPGroup 2 P) (hPX : P ≤ X)
    (hXP : X ≤ Subgroup.normalizer (P : Set G)) (hA : IsPGroup 2 A) (hAX : A ≤ X)
    (hDX : D ≤ X) (hDA : D ≤ Subgroup.centralizer (A : Set G)) (hD : Odd (Nat.card D))
    (hN : X ⊓ Subgroup.centralizer (A : Set G) ≤ Subgroup.normalizer (D : Set G)) :
    D ≤ Subgroup.centralizer (P : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hDN : D ≤ Subgroup.normalizer (P : Set G) := hDX.trans hXP
  have hAN : A ≤ Subgroup.normalizer (P : Set G) := hAX.trans hXP
  let α : ↥D →* MulAut ↥P := P.normalizerMonoidHom.comp (Subgroup.inclusion hDN)
  let β : ↥A →* MulAut ↥P := P.normalizerMonoidHom.comp (Subgroup.inclusion hAN)
  have hα : ∀ (d : ↥D) (r : ↥P), ((α d r : ↥P) : G) = (d : G) * r * (d : G)⁻¹ := fun _ _ => rfl
  have hβ : ∀ (a : ↥A) (r : ↥P), ((β a r : ↥P) : G) = (a : G) * r * (a : G)⁻¹ := fun _ _ => rfl
  have hcomm : ∀ d a, α d * β a = β a * α d := by
    intro d a
    ext r
    simp only [MulAut.mul_apply]
    rw [hα, hβ, hβ, hα]
    have hda : (d : G) * a = a * d := (Subgroup.mem_centralizer_iff.1 (hDA d.2) a a.2).symm
    calc (d : G) * ((a : G) * r * (a : G)⁻¹) * (d : G)⁻¹
        = ((d : G) * a) * r * ((d : G) * a)⁻¹ := by group
      _ = ((a : G) * d) * r * ((a : G) * d)⁻¹ := by rw [hda]
      _ = (a : G) * ((d : G) * r * (d : G)⁻¹) * (a : G)⁻¹ := by group
  have hcop : Nat.Coprime (Nat.card D) (Nat.card P) := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hP
    rw [hn]
    exact Nat.Coprime.pow_right n (Nat.coprime_two_right.2 hD)
  have hdisj := Subgroup.disjoint_of_coprime_natCard hcop
  have hfix : ∀ d r, (∀ a, β a r = r) → α d r = r := by
    intro d r hr
    have hrA : (r : G) ∈ Subgroup.centralizer (A : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      have h := congrArg Subtype.val (hr ⟨a, ha⟩)
      rw [hβ] at h
      calc a * (r : G) = a * r * a⁻¹ * a := by group
        _ = r * a := by rw [h]
    have hrN : (r : G) ∈ Subgroup.normalizer (D : Set G) := hN ⟨hPX r.2, hrA⟩
    have hc : (d : G) * r * (d : G)⁻¹ * (r : G)⁻¹ ∈ D := by
      have h1 : (r : G) * (d : G)⁻¹ * (r : G)⁻¹ ∈ D :=
        (Subgroup.mem_normalizer_iff.1 hrN _).1 (D.inv_mem d.2)
      have h2 := D.mul_mem d.2 h1
      simpa [mul_assoc] using h2
    have hcP : (d : G) * r * (d : G)⁻¹ * (r : G)⁻¹ ∈ P :=
      P.mul_mem ((Subgroup.mem_normalizer_iff.1 (hDN d.2) _).1 r.2) (P.inv_mem r.2)
    have h1 : (d : G) * r * (d : G)⁻¹ * (r : G)⁻¹ = 1 := Subgroup.disjoint_def.1 hdisj hc hcP
    apply Subtype.ext
    rw [hα]
    exact mul_inv_eq_one.1 h1
  have hD2 : ¬ 2 ∣ Nat.card ↥D := fun h2 => (Nat.not_even_iff_odd.2 hD) (even_iff_two_dvd.2 h2)
  have htriv := CFSG.GroupTheory.thompson_A_times_B hP hD2 hA α β hcomm hfix
  intro d hd
  rw [Subgroup.mem_centralizer_iff]
  intro r hr
  have h := congrArg Subtype.val (DFunLike.congr_fun (htriv ⟨d, hd⟩) ⟨r, hr⟩)
  rw [hα, MulAut.one_apply] at h
  exact (mul_inv_eq_iff_eq_mul.1 h).symm

omit [Finite G] in
theorem pow_sq_eq_self {d : G} (hodd : Odd (orderOf d)) :
    ∃ k : ℕ, (d ^ 2) ^ k = d := by
  obtain ⟨m, hm⟩ := hodd
  refine ⟨m + 1, ?_⟩
  rw [← pow_mul, show 2 * (m + 1) = orderOf d + 1 by omega, pow_succ, pow_orderOf_eq_one, one_mul]

omit [Finite G] in
theorem commute_of_inverts {z d o : G} (hd : z⁻¹ * d * z = d⁻¹) (ho : z⁻¹ * o * z = o⁻¹)
    (hdo : z⁻¹ * (d * o * d⁻¹) * z = (d * o * d⁻¹)⁻¹) (hodd : Odd (orderOf d)) :
    d * o = o * d := by
  have hd' : z⁻¹ * d⁻¹ * z = d := by
    have h1 : z⁻¹ * d⁻¹ * z = (z⁻¹ * d * z)⁻¹ := by group
    rw [h1, hd, inv_inv]
  have h1 : z⁻¹ * (d * o * d⁻¹) * z = d⁻¹ * o⁻¹ * d := by
    calc z⁻¹ * (d * o * d⁻¹) * z = (z⁻¹ * d * z) * (z⁻¹ * o * z) * (z⁻¹ * d⁻¹ * z) := by group
      _ = d⁻¹ * o⁻¹ * d := by rw [hd, ho, hd']
  have h3 : (d * o * d⁻¹)⁻¹ = d * o⁻¹ * d⁻¹ := by group
  rw [h1, h3] at hdo
  have h2 : d * d * o⁻¹ = o⁻¹ * (d * d) := by
    calc d * d * o⁻¹ = d * (d * o⁻¹ * d⁻¹) * d := by group
      _ = d * (d⁻¹ * o⁻¹ * d) * d := by rw [hdo]
      _ = o⁻¹ * (d * d) := by group
  have hc : Commute (d ^ 2) o := by
    rw [sq]
    exact Commute.inv_right_iff.1 (show Commute (d * d) o⁻¹ from h2)
  obtain ⟨k, hk⟩ := pow_sq_eq_self hodd
  have := hc.pow_left k
  rw [hk] at this
  exact this.eq

omit [Finite G] in
theorem mem_normalizer_of_inverts {K : Subgroup G} {z d : G}
    (hz : z ∈ Subgroup.normalizer (K : Set G))
    (hz' : z ∈ Subgroup.normalizer ((CFSG.conjugate K d : Subgroup G) : Set G))
    (hd : z⁻¹ * d * z = d⁻¹) (hodd : Odd (orderOf d)) : d ∈ Subgroup.normalizer (K : Set G) := by
  have h1 : CFSG.conjugate K z = K := BenderBranch.conjugate_eq_iff_mem_normalizer.2 hz
  have h2 : CFSG.conjugate (CFSG.conjugate K d) z = CFSG.conjugate K d :=
    BenderBranch.conjugate_eq_iff_mem_normalizer.2 hz'
  have h3 : d * z = z * d⁻¹ := by
    calc d * z = z * (z⁻¹ * d * z) := by group
      _ = z * d⁻¹ := by rw [hd]
  rw [BenderBranch.conjugate_conjugate, h3, ← BenderBranch.conjugate_conjugate, h1] at h2
  have h4 : CFSG.conjugate K (d ^ 2) = K := by
    have h5 := congrArg (fun H => CFSG.conjugate H d) h2
    simp only [BenderBranch.conjugate_conjugate, inv_mul_cancel, BenderBranch.conjugate_one] at h5
    rw [sq]
    exact h5.symm
  have h6 : d ^ 2 ∈ Subgroup.normalizer (K : Set G) :=
    BenderBranch.conjugate_eq_iff_mem_normalizer.1 h4
  obtain ⟨k, hk⟩ := pow_sq_eq_self hodd
  rw [← hk]
  exact Subgroup.pow_mem _ h6 k

theorem commutator_eq_bot_of_odd {K D : Subgroup G} (hK : CFSG.IsQuasisimple ↥K)
    (hD : Odd (Nat.card D)) (hDK : D ≤ Subgroup.normalizer (K : Set G))
    (hKD : K ≤ Subgroup.normalizer (D : Set G)) : ⁅K, D⁆ = ⊥ := by
  have hCK : ⁅K, D⁆ ≤ K := Subgroup.le_normalizer_iff_commutator_le_left.mp hDK
  have hCD : ⁅K, D⁆ ≤ D := Subgroup.le_normalizer_iff_commutator_le_right.mp hKD
  have hCn : (⁅K, D⁆.subgroupOf K).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (Subgroup.normalizer_commutator_ge_left K D)
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hK hCn with htop | hcen
  · exfalso
    have hKC : K ≤ ⁅K, D⁆ := fun k hk => by
      have hk' : (⟨k, hk⟩ : K) ∈ ⁅K, D⁆.subgroupOf K := htop ▸ Subgroup.mem_top _
      exact hk'
    have h2 : 2 ∣ Nat.card D :=
      (two_dvd_card_of_isQuasisimple hK).trans (Subgroup.card_dvd_of_le (hKC.trans hCD))
    exact (Nat.not_even_iff_odd.2 hD) (even_iff_two_dvd.2 h2)
  · apply CFSG.LocalCores.perfect_double_commutator hK.1
    rw [eq_bot_iff, Subgroup.commutator_le]
    intro c hc k hk
    have hcZ : (⟨c, hCK hc⟩ : K) ∈ Subgroup.center K := hcen hc
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
    exact (congrArg Subtype.val (Subgroup.mem_center_iff.1 hcZ ⟨k, hk⟩)).symm

theorem fitting_le_pCore_sup_oddCore (X : Type) [Group X] [Finite X] :
    CFSG.fittingSubgroup X ≤ CFSG.pCore 2 X ⊔ CFSG.oddCore X :=
  CFSG.WholeGroup.fittingSubgroup_le_pCore_two_sup_oddCore

theorem le_oddCoreIn_of_centralizes {X D : Subgroup G} (hDX : D ≤ X) (hD : Odd (Nat.card D))
    (h2 : D ≤ Subgroup.centralizer (pCoreOf 2 X : Set G))
    (hO : D ≤ Subgroup.centralizer (oddCoreIn X : Set G))
    (hE : ∀ K : Subgroup G, IsComponentIn K X → D ≤ Subgroup.centralizer (K : Set G)) :
    D ≤ oddCoreIn X := by
  classical
  set D' : Subgroup ↥X := D.subgroupOf X with hD'def
  have hC : ∀ S : Subgroup ↥X, (∀ s ∈ S, (s : G) ∈ Subgroup.centralizer (D : Set G)) →
      S ≤ Subgroup.centralizer (D' : Set ↥X) := by
    intro S hS s hs
    rw [Subgroup.mem_centralizer_iff]
    intro d hd
    exact Subtype.ext (Subgroup.mem_centralizer_iff.1 (hS s hs) d hd)
  have hF : CFSG.generalizedFitting ↥X ≤ Subgroup.centralizer (D' : Set ↥X) := by
    refine sup_le ((fitting_le_pCore_sup_oddCore ↥X).trans (sup_le ?_ ?_)) ?_
    · refine hC _ fun s hs => ?_
      have hs' : s ∈ CFSG.Open.pCore 2 ↥X := hs
      have hsP : (s : G) ∈ pCoreOf 2 X := ⟨s, hs', rfl⟩
      exact Subgroup.mem_centralizer_iff.2 fun d hd =>
        (Subgroup.mem_centralizer_iff.1 (h2 hd) s hsP).symm
    · refine hC _ fun s hs => ?_
      have hsO : (s : G) ∈ oddCoreIn X := (mem_oddCoreIn_iff X s).2 hs
      exact Subgroup.mem_centralizer_iff.2 fun d hd =>
        (Subgroup.mem_centralizer_iff.1 (hO hd) s hsO).symm
    · refine sSup_le fun K' hK' => hC _ fun s hs => ?_
      have hKc : IsComponentIn (K'.map X.subtype) X :=
        ⟨Subgroup.map_subtype_le K', by rw [A4.subgroupOf_map_subtype' X K']; exact hK'⟩
      have hsK : (s : G) ∈ K'.map X.subtype := ⟨s, hs, rfl⟩
      exact Subgroup.mem_centralizer_iff.2 fun d hd =>
        (Subgroup.mem_centralizer_iff.1 (hE _ hKc hd) s hsK).symm
  set Z' := Subgroup.centralizer (CFSG.generalizedFitting ↥X : Set ↥X) with hZ'def
  have hDZ' : D' ≤ Z' := Subgroup.le_centralizer_iff.1 hF
  have hZF : Z' ≤ CFSG.generalizedFitting ↥X := CFSG.centralizer_generalizedFitting_le ↥X
  set Z := Z'.map X.subtype with hZdef
  have hZX : Z ≤ X := Subgroup.map_subtype_le Z'
  have hZsub : (Z.subgroupOf X).IsSubnormal := by
    rw [hZdef, A4.subgroupOf_map_subtype' X Z']
    have : Z'.Normal := inferInstance
    exact Subgroup.Normal.isSubnormal this
  have hDZ : D ≤ Z := fun d hd => ⟨⟨d, hDX hd⟩, hDZ' hd, rfl⟩
  have hZC : Z ≤ Subgroup.centralizer (D : Set G) := by
    rintro _ ⟨x, hx, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro d hd
    obtain ⟨y, hy, hyd⟩ := hDZ hd
    rw [← hyd]
    exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.1 hx y (hZF hy))
  have h1 : D ≤ oddCoreIn Z :=
    le_oddCoreIn_of_odd hDZ (hZC.trans (Subgroup.centralizer_le_normalizer _)) hD
  exact h1.trans (oddCoreIn_le_of_subnormal'' hZX hZsub)

end Tools

section Setting

variable {G : Type} [Group G] [Finite G] {T M V U : Subgroup G}

omit [Finite G] in
theorem centralizer_singleton_eq_inf (z : G) :
    Subgroup.centralizer ({z} : Set G) =
      Subgroup.normalizer ((Subgroup.zpowers z : Subgroup G) : Set G) ⊓
        Subgroup.centralizer ((Subgroup.zpowers z : Subgroup G) : Set G) := by
  ext g
  constructor
  · intro hg
    have hgz : g * z = z * g := Subgroup.mem_centralizer_singleton_iff.1 hg
    have hgZ : g ∈ Subgroup.centralizer ((Subgroup.zpowers z : Subgroup G) : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨k, rfl⟩
      exact ((Commute.zpow_left hgz.symm k).symm).eq.symm
    exact ⟨Subgroup.centralizer_le_normalizer _ hgZ, hgZ⟩
  · rintro ⟨-, hg⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.1 hg z (Subgroup.mem_zpowers z)).symm

theorem exists_center_involution (h : HypE61 T M V) :
    ∃ z ∈ V, z ∈ T ⊓ Subgroup.centralizer (T : Set G) ∧ z ≠ 1 ∧
      CharTwo (Subgroup.centralizer ({z} : Set G)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨z, hzV, hzT, hz1⟩ : ∃ z ∈ V, z ∈ T ⊓ Subgroup.centralizer (T : Set G) ∧ z ≠ 1 := by
    have hT2 : IsPGroup 2 T := h.sylow.1
    have : Group.IsNilpotent T := hT2.isNilpotent
    have hnormal : (V.subgroupOf T).Normal := Subgroup.normal_subgroupOf_of_le_normalizer h.normal
    have hne : V.subgroupOf T ≠ ⊥ := by
      intro h0
      apply h.ne_bot
      rw [← Subgroup.map_subgroupOf_eq_of_le h.le, h0, Subgroup.map_bot]
    obtain ⟨⟨y, hy⟩, hy1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
      (Group.IsNilpotent.inf_center_ne_bot_of_normal hne)
    refine ⟨y, hy.1, ⟨y.2, Subgroup.mem_centralizer_iff.2 fun t ht =>
      congrArg Subtype.val (Subgroup.mem_center_iff.mp hy.2 ⟨t, ht⟩)⟩, fun h1 => hy1 ?_⟩
    exact Subtype.ext (Subtype.ext h1)
  refine ⟨z, hzV, hzT, hz1, ?_⟩
  have hz2 : z ^ 2 = 1 := h.isElemAbelian.2 z hzV
  have hZ2 : IsPGroup 2 (Subgroup.zpowers z) := by
    rintro ⟨_, k, rfl⟩
    refine ⟨1, Subtype.ext ?_⟩
    show (z ^ k) ^ 2 ^ 1 = 1
    rw [pow_one, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hz2, one_zpow]
  have hCz := centralizer_singleton_eq_inf z
  have hTsyl : IsSylowTwoOf T ⊤ :=
    ⟨le_top, h.sylow.1, by rw [← Subgroup.relIndex, Subgroup.relIndex_top_right]; exact h.sylow.2⟩
  have hZT : Subgroup.zpowers z ⊓ (T ⊓ Subgroup.centralizer (T : Set G)) ≠ ⊥ := by
    intro h0
    apply hz1
    have : z ∈ Subgroup.zpowers z ⊓ (T ⊓ Subgroup.centralizer (T : Set G)) :=
      ⟨Subgroup.mem_zpowers z, hzT⟩
    rw [h0] at this
    exact this
  have hNz := CT.charTwo_normalizer_of_inf_center h.qtke.2.1 hTsyl hZ2 hZT
  rw [hCz]
  exact CT.CharTwo.inf_centralizer hNz Subgroup.le_normalizer hZ2

theorem lemma115Hyp_of_mem_gamma (h : HypE61 T M V) (hU : U ∈ gammaE64 V M) {z : G}
    (hzV : z ∈ V) (hz1 : z ≠ 1) (hCz2 : CharTwo (Subgroup.centralizer ({z} : Set G))) :
    Lemma115Hyp (Subgroup.centralizer (U : Set G)) (T ⊓ Subgroup.centralizer (V : Set G))
      (Subgroup.centralizer ({z} : Set G)) z := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H := Subgroup.centralizer (U : Set G) with hHdef
  set Q := T ⊓ Subgroup.centralizer (V : Set G) with hQdef
  have hQH : IsSylowTwoOf Q H := e6_5_one h hU
  have hVQ : V ≤ Q := h.le_inf_centralizer
  have hQV : Q ≤ Subgroup.centralizer (V : Set G) := inf_le_right
  have hUV : U ≤ V := hU.1
  have hVc : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := fun a ha b hb =>
    B2F.isElemAbelian_comm h.isElemAbelian ha hb
  have hz2 : z ^ 2 = 1 := h.isElemAbelian.2 z hzV
  have hZ2 : IsPGroup 2 (Subgroup.zpowers z) := by
    rintro ⟨_, k, rfl⟩
    refine ⟨1, Subtype.ext ?_⟩
    show (z ^ k) ^ 2 ^ 1 = 1
    rw [pow_one, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hz2, one_zpow]
  have hCz := centralizer_singleton_eq_inf z
  have hzQ : z ∈ Q := hVQ hzV
  have hzC : z ∈ Subgroup.centralizer ({z} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.2 rfl
  have hUz : U ≤ pCoreOf 2 (H ⊓ Subgroup.centralizer ({z} : Set G)) := by
    refine C1.le_pCoreOf_of_normalized (le_inf (fun u hu => ?_) (fun u hu => ?_)) (fun g hg => ?_)
      (h.isPGroup_V.to_le hUV)
    · exact Subgroup.mem_centralizer_iff.2 fun u' hu' => hVc _ (hUV hu') _ (hUV hu)
    · exact Subgroup.mem_centralizer_singleton_iff.2 (hVc _ (hUV hu) _ hzV)
    · exact Subgroup.centralizer_le_normalizer _ hg.1
  exact
    { pCore_ne_bot := fun h0 => hU.2.1 (le_bot_iff.1 (h0 ▸ (C1.le_pCoreOf_of_normalized
        (fun u hu => Subgroup.mem_centralizer_iff.2 fun u' hu' => hVc _ (hUV hu') _ (hUV hu))
        (Subgroup.centralizer_le_normalizer _) (h.isPGroup_V.to_le hUV))))
      sylow := hQH
      charTwo := hCz2
      pCore_M_ne_bot := fun h0 => hz1 (by
        have hle : Subgroup.zpowers z ≤ pCoreOf 2 (Subgroup.centralizer ({z} : Set G)) :=
          C1.le_pCoreOf_of_normalized (Subgroup.zpowers_le.2 hzC) (by
            rw [hCz]; exact inf_le_left) hZ2
        have := hle (Subgroup.mem_zpowers z)
        rw [h0] at this
        exact this)
      le := fun q hq => Subgroup.mem_centralizer_singleton_iff.2
        (Subgroup.mem_centralizer_iff.1 (hQV hq) z hzV).symm
      centralizer_le := fun g hg => Subgroup.centralizer_le hUz hg.2
      centralizer_z_le := le_rfl
      z_ne_one := hz1
      z_mem := hzQ
      z_central := Subgroup.mem_centralizer_iff.2 fun q hq =>
        (Subgroup.mem_centralizer_iff.1 (hQV hq) z hzV).symm
      z_sq := hz2 }

end Setting

theorem e619_of (h311 : Theorem311Stmt) (hlist : Lemma115_3_List) (h618 : E618Stmt)
    (hP3 : E619Insp) : E619Stmt := by
  intro G _ _ T M V W W₀ hV h h15 hWV hW1 hW₀V hW₀1
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := h.simple
  have hV2 : IsPGroup 2 V := h.isPGroup_V
  have hVc : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := fun a ha b hb =>
    B2F.isElemAbelian_comm h.isElemAbelian ha hb
  set H := Subgroup.centralizer (W : Set G) with hHdef
  set D := oddCoreIn H with hDdef
  by_cases hO : D = ⊥
  · rw [hO]
    exact bot_le
  have hWM : ¬ H ≤ M := e6_16_two h hWV fun hc => hO (oddCoreIn_eq_bot_of_charTwo' hc)
  obtain ⟨hr, hm, hWΓ⟩ := e6_16_one hV h h15 hWV hW1 hWM
  have h6 : 6 ≤ E3.mQuot V ⊥ := (e6_17 h311 hV h h15 hr).2
  set U₁ := W ⊓ W₀ with hU₁def
  by_cases hWU : U₁ = W
  · rw [hWU]
  have hU₁W : U₁ ≤ W := inf_le_left
  have hU₁V : U₁ ≤ V := hU₁W.trans hWV
  have hW2 : IsPGroup 2 W := hV2.to_le hWV
  have hq1 : E3.mQuot W U₁ = 1 := by
    have h1 : E3.mQuot W U₁ ≤ E3.mQuot V W₀ := mQuot_inf_left_le hV2 hWV
    have h0 : E3.mQuot W U₁ ≠ 0 := fun h0 => hWU ((E3.mQuot_eq_zero_iff hW2 hU₁W).1 h0)
    omega
  have hq2 : E3.mQuot V U₁ = 2 := by
    rw [E3.mQuot_add hU₁W hWV, hq1, hW1]
  have hU₁1 : U₁ ≠ ⊥ := by
    intro h0
    rw [h0] at hq2
    omega
  set H₁ := Subgroup.centralizer (U₁ : Set G) with hH₁def
  have hHH₁ : H ≤ H₁ := Subgroup.centralizer_le hU₁W
  have hH₁M : ¬ H₁ ≤ M := fun hle => hWM (hHH₁.trans hle)
  have hU₁Γ : U₁ ∈ gammaE64 V M := mem_gammaE64_of_mQuot_lt hV h hU₁V hU₁1 hH₁M (by omega)
  obtain ⟨z, hzV, -, hz1, hCz2⟩ := exists_center_involution h
  have h115 := lemma115Hyp_of_mem_gamma h hWΓ hzV hz1 hCz2
  have h115₁ := lemma115Hyp_of_mem_gamma h hU₁Γ hzV hz1 hCz2
  have hinvD : ∀ d ∈ D, z⁻¹ * d * z = d⁻¹ := h115.inverts_oddCoreIn
  have hinvO : ∀ o ∈ oddCoreIn H₁, z⁻¹ * o * z = o⁻¹ := h115₁.inverts_oddCoreIn
  have hDodd : Odd (Nat.card D) := odd_card_oddCoreIn H
  have hDH : D ≤ H := oddCoreIn_le H
  have hDH₁ : D ≤ H₁ := hDH.trans hHH₁
  have hordD : ∀ d ∈ D, Odd (orderOf d) := fun d hd =>
    Odd.of_dvd_nat hDodd (Subgroup.orderOf_dvd_natCard D hd)
  set Q := T ⊓ Subgroup.centralizer (V : Set G) with hQdef
  have hQH₁ : IsSylowTwoOf Q H₁ := e6_5_one h hU₁Γ
  have hVQ : V ≤ Q := h.le_inf_centralizer
  have hcenQ : ∀ v ∈ V, v ∈ Subgroup.centralizer (Q : Set G) := fun v hv =>
    Subgroup.mem_centralizer_iff.2 fun q hq => (Subgroup.mem_centralizer_iff.1 hq.2 v hv).symm
  have hWH₁ : W ≤ H₁ := fun w hw =>
    Subgroup.mem_centralizer_iff.2 fun x hx => hVc _ (hU₁V hx) _ (hWV hw)
  refine le_oddCoreIn_of_centralizes hDH₁ hDodd ?_ ?_ ?_
  ·
    have hN : H₁ ⊓ Subgroup.centralizer (W : Set G) ≤ Subgroup.normalizer (D : Set G) := by
      rw [inf_eq_right.2 hHH₁]
      exact le_normalizer_oddCoreIn H
    exact le_centralizer_of_AxB (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 H₁)
      (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 H₁)
      (CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 H₁) hW2 hWH₁ hDH₁
      hDH hDodd hN
  ·
    intro d hd
    rw [Subgroup.mem_centralizer_iff]
    intro o ho
    have hdo : d * o * d⁻¹ ∈ oddCoreIn H₁ :=
      (Subgroup.mem_normalizer_iff.1 (le_normalizer_oddCoreIn H₁ (hDH₁ hd)) o).1 ho
    exact (commute_of_inverts (hinvD d hd) (hinvO o ho) (hinvO _ hdo) (hordD d hd)).symm
  ·
    intro K hK
    have hKq : CFSG.IsQuasisimple ↥K := BenderBranch.isQuasisimple_of_isComponentIn hK
    have hzK : z ∈ Subgroup.normalizer (K : Set G) :=
      mem_normalizer_of_mem_center_sylow hQH₁ hK (hVQ hzV) (hcenQ z hzV)
    have hDK : D ≤ Subgroup.normalizer (K : Set G) := fun d hd =>
      mem_normalizer_of_inverts hzK (mem_normalizer_of_mem_center_sylow hQH₁
        (Unc25G2.isComponentIn_conjugate hK (hDH₁ hd)) (hVQ hzV) (hcenQ z hzV))
        (hinvD d hd) (hordD d hd)
    obtain ⟨u, huW, huU₁⟩ : ∃ u ∈ W, u ∉ U₁ := by
      by_contra hall
      push Not at hall
      exact hWU (le_antisymm hU₁W hall)
    have huV : u ∈ V := hWV huW
    have hidx : U₁.relIndex W = 2 := by rw [E3.relIndex_eq_two_pow hW2, hq1, pow_one]
    have hCW := centralizer_eq_inf_of_relIndex_two hU₁W hidx huW huU₁
    by_cases huK : u ∈ Subgroup.centralizer (K : Set G)
    ·
      have hKH : K ≤ H := by
        show K ≤ Subgroup.centralizer (W : Set G)
        rw [hCW]
        exact le_inf hK.1 fun k hk => Subgroup.mem_centralizer_singleton_iff.2
          (Subgroup.mem_centralizer_iff.1 huK k hk)
      have hc := commutator_eq_bot_of_odd hKq hDodd hDK (hKH.trans (le_normalizer_oddCoreIn H))
      exact Subgroup.le_centralizer_iff.1 (Subgroup.commutator_eq_bot_iff_le_centralizer.1 hc)
    ·
      by_contra hDK'
      set R := Q ⊓ Subgroup.normalizer (K : Set G) with hRdef
      have hRK : R ⊓ K = Q ⊓ K := by
        rw [hRdef, inf_assoc, inf_eq_right.2 (Subgroup.le_normalizer : K ≤ _)]
      have hSK : IsSylowTwoOf (Q ⊓ K) K := isSylowTwoOf_inf_of_subnormal' hQH₁ hK.1 hK.2.2
      have hcases := (Lemma115_3_List.component_cases hlist h.simple h.nonabelian
        (qtkeCore_of_cat h.nonabelian h.qtke) h115₁ hK).2.2.2
      have huN : u ∈ Subgroup.normalizer (K : Set G) :=
        mem_normalizer_of_mem_center_sylow hQH₁ hK (hVQ huV) (hcenQ u huV)
      have hcenR : ∀ v ∈ V, v ∈ Subgroup.centralizer (R : Set G) := fun v hv =>
        Subgroup.centralizer_le (inf_le_left : R ≤ Q) (hcenQ v hv)
      have hDu : D ≤ Subgroup.centralizer ({u} : Set G) := fun d hd =>
        Subgroup.mem_centralizer_singleton_iff.2
          (Subgroup.mem_centralizer_iff.1 (hDH hd) u huW).symm
      have hA7 := hP3 G K R D z u hKq hcases (h.isPGroup_Q.to_le inf_le_left) inf_le_right
        (by rw [hRK]; exact hSK) ⟨hVQ hzV, hzK⟩ (hcenR z hzV) (h.isElemAbelian.2 z hzV)
        ⟨hVQ huV, huN⟩ (hcenR u huV) (h.isElemAbelian.2 u huV) huK hDodd hDK hDu hinvD hDK'
      exact h618 G T M V U₁ K hV h h15 hU₁Γ (by omega) hK hA7

end E6

end CFSG.Quasithin
