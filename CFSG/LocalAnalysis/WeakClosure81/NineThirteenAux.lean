module

public import CFSG.LocalAnalysis.WeakClosure81.EightFour
public import CFSG.Quasithin.Background.E3Gen
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.WeakClosure81.NineDefs

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.CGT.Timmesfeld75 Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G] {V T X : Subgroup G}

private theorem nineThirteenAux_inf_center_ne_bot {T U : Subgroup G} (hT : IsPGroup 2 T)
    (hUT : U ≤ T) (hUn : T ≤ Subgroup.normalizer (U : Set G)) (hU : U ≠ ⊥) :
    U ⊓ (T ⊓ Subgroup.centralizer (T : Set G)) ≠ ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Group.IsNilpotent T := hT.isNilpotent
  haveI : (U.subgroupOf T).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hUn
  have hne : U.subgroupOf T ≠ ⊥ := by
    intro h
    apply hU
    rw [← Subgroup.map_subgroupOf_eq_of_le hUT, h, Subgroup.map_bot]
  obtain ⟨⟨y, hy⟩, hy1⟩ :=
    Subgroup.ne_bot_iff_exists_ne_one.mp (Group.IsNilpotent.inf_center_ne_bot_of_normal hne)
  have hyC : (y : G) ∈ Subgroup.centralizer (T : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hy.2 ⟨t, ht⟩)
  intro h
  have hmem : (y : G) ∈ U ⊓ (T ⊓ Subgroup.centralizer (T : Set G)) := ⟨hy.1, y.2, hyC⟩
  rw [h, Subgroup.mem_bot] at hmem
  exact hy1 (Subtype.ext (Subtype.ext hmem))

private theorem nineThirteenAux_mem_sup_iff {X T : Subgroup G}
    (hXT : (X : Set G) * T = T * X) (z : G) :
    z ∈ X ⊔ T ↔ ∃ t ∈ T, ∃ x ∈ X, t * x = z := by
  let S : Subgroup G :=
    { carrier := (T : Set G) * X
      one_mem' := ⟨1, T.one_mem, 1, X.one_mem, by group⟩
      mul_mem' := by
        rintro _ _ ⟨t₁, ht₁, x₁, hx₁, rfl⟩ ⟨t₂, ht₂, x₂, hx₂, rfl⟩
        have h : x₁ * t₂ ∈ (X : Set G) * T := ⟨x₁, hx₁, t₂, ht₂, rfl⟩
        rw [hXT] at h
        obtain ⟨t', ht', x', hx', hx't'⟩ := h
        change t' * x' = x₁ * t₂ at hx't'
        refine ⟨t₁ * t', T.mul_mem ht₁ ht', x' * x₂, X.mul_mem hx' hx₂, ?_⟩
        calc (t₁ * t') * (x' * x₂) = t₁ * (t' * x') * x₂ := by group
          _ = t₁ * (x₁ * t₂) * x₂ := by rw [hx't']
          _ = (t₁ * x₁) * (t₂ * x₂) := by group
      inv_mem' := by
        rintro _ ⟨t, ht, x, hx, rfl⟩
        have h : x⁻¹ * t⁻¹ ∈ (X : Set G) * T :=
          ⟨x⁻¹, X.inv_mem hx, t⁻¹, T.inv_mem ht, rfl⟩
        rw [hXT] at h
        obtain ⟨t', ht', x', hx', hx't'⟩ := h
        change t' * x' = x⁻¹ * t⁻¹ at hx't'
        exact ⟨t', ht', x', hx', by
          change t' * x' = ((fun x1 x2 : G => x1 * x2) t x)⁻¹
          rw [hx't']
          group⟩ }
  have hScar : (S : Set G) = (T : Set G) * X := rfl
  have hle : X ⊔ T ≤ S := sup_le
    (fun x hx => ⟨1, T.one_mem, x, hx, by group⟩)
    (fun t ht => ⟨t, ht, 1, X.one_mem, by group⟩)
  constructor
  · intro hz
    have hz' : z ∈ (T : Set G) * X := hScar ▸ hle hz
    obtain ⟨t, ht, x, hx, htx⟩ := Set.mem_mul.1 hz'
    change t * x = z at htx
    exact ⟨t, ht, x, hx, htx⟩
  · rintro ⟨t, ht, x, hx, hxt⟩
    change t * x = z at hxt
    rw [← hxt]
    rw [sup_comm]
    exact Subgroup.mul_mem_sup ht hx

theorem exists_conj_sylow_centralizer (h9 : Hyp9 V T) :
    ∃ A : Subgroup G, IsGConj V A ∧ A ≤ T ∧ A ≠ V ∧
      IsSylowIn 2 (T ⊓ centralizer (A : Set G))
        (normalizer (V : Set G) ⊓ centralizer (A : Set G)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hVnorm : (V.subgroupOf (normalizer (V : Set G))).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer Subgroup.le_normalizer).2 le_rfl
  have hVp : IsPGroup 2 V := B2F.isPGroup_of_isElemAbelian h9.hyp7.1
  have hVT : V ≤ T := h9.sylow.le_of_normal Subgroup.le_normalizer hVnorm hVp
  have hTM : T ≤ normalizer (V : Set G) := h9.sylow.le
  have hTp : IsPGroup 2 T := h9.sylow.isPGroup
  have hb : ∃ g : G, conjSubgroup V g ≤ T ∧ ¬ conjSubgroup V g ≤ V := by
    by_contra h
    have hcon : ∀ g : G, conjSubgroup V g ≤ T → conjSubgroup V g ≤ V := by
      intro g hg
      by_contra hgV
      exact h ⟨g, hg, hgV⟩
    have hle1 : E3.wClos V 0 T ≤ V := by
      rw [wClos_zero_eq_iSup h9.hyp7.1]
      exact iSup₂_le fun g hg => hcon g hg
    have hle2 : V ≤ E3.wClos V 0 T := by
      rw [wClos_zero_eq_iSup h9.hyp7.1]
      exact le_iSup₂_of_le 1 (by rwa [CFSG.Quasithin.conjSubgroup_one])
        (le_of_eq (CFSG.Quasithin.conjSubgroup_one V).symm)
    exact h9.ne (le_antisymm hle1 hle2).symm
  obtain ⟨g, hA₀T, hA₀V⟩ := hb
  have hA₀ab : IsMulCommutative ↥(conjSubgroup V g) :=
    (E3.isElemAbelian_conjSubgroup h9.hyp7.1 g).1
  have hA₀2 : IsPGroup 2 (conjSubgroup V g) :=
    B2F.isPGroup_of_isElemAbelian (E3.isElemAbelian_conjSubgroup h9.hyp7.1 g)
  have hA₀leC : conjSubgroup V g ≤ centralizer (conjSubgroup V g : Set G) :=
    Subgroup.le_centralizer_iff_isMulCommutative.mpr hA₀ab
  have hA₀C₀ : conjSubgroup V g ≤
      normalizer (V : Set G) ⊓ centralizer (conjSubgroup V g : Set G) :=
    le_inf (hA₀T.trans hTM) hA₀leC
  obtain ⟨P, hPsyl, hA₀P⟩ := exists_isSylowIn_ge 2 hA₀C₀ hA₀2
  have hPM : P ≤ normalizer (V : Set G) := hPsyl.le.trans inf_le_left
  have hPp : IsPGroup 2 P := hPsyl.isPGroup
  obtain ⟨m, hmM, hmP⟩ :=
    exists_conj_le_of_isSylowTwoOf
      (show CFSG.QuasithinUnique.IsSylowTwoOf T (normalizer (V : Set G)) from h9.sylow)
      hPM hPp
  have hnM : m⁻¹ ∈ normalizer (V : Set G) := inv_mem hmM
  have hP'eq : conjSubgroup P m⁻¹ = cjSub m P := by
    ext x
    simp [mem_cjSub, mem_conjSubgroup_iff]
  have hP'T : conjSubgroup P m⁻¹ ≤ T := (le_of_eq hP'eq).trans hmP
  have hMconj : conjSubgroup (normalizer (V : Set G)) m⁻¹ = normalizer (V : Set G) :=
    (conjSubgroup_eq_iff_mem_normalizer).2 (Subgroup.le_normalizer hnM)
  have hCn : conjSubgroup (normalizer (V : Set G) ⊓ centralizer (conjSubgroup V g : Set G)) m⁻¹ =
      normalizer (V : Set G) ⊓
        centralizer (conjSubgroup (conjSubgroup V g) m⁻¹ : Set G) := by
    rw [E3.conjSubgroup_inf, E3.conjSubgroup_centralizer, hMconj]
  have hP'C : IsSylowIn 2 (conjSubgroup P m⁻¹)
      (conjSubgroup (normalizer (V : Set G) ⊓ centralizer (conjSubgroup V g : Set G)) m⁻¹) :=
    ⟨E3.conjSubgroup_mono_left m⁻¹ hPsyl.le, E3.isPGroup_conjSubgroup hPsyl.isPGroup m⁻¹,
      by rw [E3.relIndex_conjSubgroup]; exact hPsyl.not_dvd_relIndex⟩
  rw [hCn] at hP'C
  refine ⟨conjSubgroup (conjSubgroup V g) m⁻¹,
    ⟨g * m⁻¹, by rw [CFSG.Quasithin.conjSubgroup_conjSubgroup]⟩, ?_, ?_, ?_⟩
  · exact (E3.conjSubgroup_mono_left m⁻¹ hA₀P).trans hP'T
  · intro hAV
    have h := congrArg (fun B : Subgroup G => conjSubgroup B m) hAV
    rw [CFSG.Quasithin.conjSubgroup_conjSubgroup, inv_mul_cancel,
      CFSG.Quasithin.conjSubgroup_one, (conjSubgroup_eq_iff_mem_normalizer).2 hmM] at h
    exact hA₀V h.le
  · have hQ_le : T ⊓ centralizer (conjSubgroup (conjSubgroup V g) m⁻¹ : Set G) ≤
        normalizer (V : Set G) ⊓ centralizer (conjSubgroup (conjSubgroup V g) m⁻¹ : Set G) :=
      le_inf (inf_le_left.trans hTM) inf_le_right
    have hQ2 : IsPGroup 2
        (T ⊓ centralizer (conjSubgroup (conjSubgroup V g) m⁻¹ : Set G) : Subgroup G) :=
      IsPGroup.to_le hTp inf_le_left
    have hP'Q : conjSubgroup P m⁻¹ ≤
        T ⊓ centralizer (conjSubgroup (conjSubgroup V g) m⁻¹ : Set G) :=
      le_inf hP'T (hP'C.le.trans inf_le_right)
    refine ⟨hQ_le, hQ2, fun hdvd => hP'C.not_dvd_relIndex ?_⟩
    exact hdvd.trans (Subgroup.relIndex_dvd_of_le_left
      (normalizer (V : Set G) ⊓ centralizer (conjSubgroup (conjSubgroup V g) m⁻¹ : Set G)) hP'Q)

theorem commutator_cClos_ne_bot_of_not_normalizer_le (h9 : Hyp9 V T) (hX : X ∈ calP V)
    (hX1 : X ≠ ⊥) (h1 : ¬ normalizer (E3.wClos V 1 T : Set G) ≤ normalizer (V : Set G)) :
    ⁅twoResidual (X ⊔ T), E3.cClos V 1 T⁆ ≠ ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hcomm
  rcases hX with ⟨p, hp, hp2, hXp, hXM, hXG, hXtriv⟩
  have hleC : twoResidual (X ⊔ T) ≤ centralizer (E3.cClos V 1 T : Set G) :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer).1 hcomm
  have hXres : X ≤ twoResidual (X ⊔ T) := by
    intro x hx
    rw [mem_twoResidual_iff]
    intro N hNH hHN hpow
    obtain ⟨k, hk⟩ := hpow x (Subgroup.mem_sup_left hx)
    obtain ⟨a, ha⟩ := hXp ⟨x, hx⟩
    have hxorder : orderOf x ∣ p ^ a := by
      apply orderOf_dvd_of_pow_eq_one
      have h := congrArg Subtype.val ha
      simpa using h
    have hcop : (2 ^ k).Coprime (orderOf x) := by
      have hp2' : (2 : ℕ).Coprime p := (Nat.coprime_primes Nat.prime_two hp).2 (Ne.symm hp2)
      have h1' : (2 ^ k).Coprime (p ^ a) := (hp2'.pow_left k).pow_right a
      exact h1'.coprime_dvd_right hxorder
    obtain ⟨j, hj⟩ := exists_pow_eq_self_of_coprime hcop
    rw [← hj]
    exact N.pow_mem hk j
  have hVnorm : (V.subgroupOf (normalizer (V : Set G))).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer Subgroup.le_normalizer).2 le_rfl
  have hVp : IsPGroup 2 V := B2F.isPGroup_of_isElemAbelian h9.hyp7.1
  have hVT : V ≤ T := h9.sylow.le_of_normal Subgroup.le_normalizer hVnorm hVp
  have hVW : V ≤ E3.wClos V 1 T := E3.le_wClos_of_mQuot_le_self h9.hyp7.1 hVT le_rfl
    (k := 1) (by rw [E3.mQuot_self]; norm_num) (by have := h9.rk_gt; omega)
  obtain ⟨h, hhN, hhM⟩ := SetLike.not_le_iff_exists.1 h1
  have hW1h : conjSubgroup (E3.wClos V 1 T) h = E3.wClos V 1 T :=
    (conjSubgroup_eq_iff_mem_normalizer).2 hhN
  have hVhW1 : conjSubgroup V h ≤ E3.wClos V 1 T := by
    have h1' : conjSubgroup V h ≤ conjSubgroup (E3.wClos V 1 T) h :=
      E3.conjSubgroup_mono_left h hVW
    rwa [hW1h] at h1'
  have hVhM : conjSubgroup V h ≤ normalizer (V : Set G) :=
    hVhW1.trans ((E3.wClos_le 1 T).trans h9.sylow.le)
  have hW1two : IsPGroup 2 (E3.wClos V 1 T) := h9.sylow.isPGroup.to_le (E3.wClos_le 1 T)
  have hW1norm : E3.wClos V 1 T ≤ normalizer (V : Set G) :=
    (E3.wClos_le 1 T).trans h9.sylow.le
  have hVne : V ≠ ⊥ := by
    intro hVbot
    have h2 := h9.hyp7.2.1
    rw [hVbot, Subgroup.card_bot] at h2
    omega
  have hb0ne : V ⊓ (E3.wClos V 1 T ⊓ centralizer (E3.wClos V 1 T : Set G)) ≠ ⊥ :=
    nineThirteenAux_inf_center_ne_bot hW1two hVW hW1norm hVne
  obtain ⟨⟨b₀, hb₀mem⟩, hb₀1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hb0ne
  have hb₀V : b₀ ∈ V := (Subgroup.mem_inf.1 hb₀mem).1
  have hb₀C : b₀ ∈ centralizer (E3.wClos V 1 T : Set G) := (Subgroup.mem_inf.1 hb₀mem).2.2
  have hb₀1' : b₀ ≠ 1 := fun hb => hb₀1 (Subtype.ext hb)
  set b : G := h⁻¹ * b₀ * h with hbdef
  have hbVh : b ∈ conjSubgroup V h := by
    rw [mem_conjSubgroup_iff]
    rw [hbdef]
    rw [show h * (h⁻¹ * b₀ * h) * h⁻¹ = b₀ by group]
    exact hb₀V
  have hb1 : b ≠ 1 := by
    intro hb
    apply hb₀1'
    have h1' : b₀ = h * b * h⁻¹ := by rw [hbdef]; group
    rw [hb] at h1'
    simpa using h1'
  have hbW : b ∈ E3.wClos V 1 T := hVhW1 hbVh
  have hbT : b ∈ T := E3.wClos_le 1 T hbW
  have hbC : b ∈ centralizer (E3.wClos V 1 T : Set G) := by
    have h1' : b ∈ conjSubgroup (centralizer (E3.wClos V 1 T : Set G)) h := by
      rw [mem_conjSubgroup_iff]
      rw [hbdef]
      rw [show h * (h⁻¹ * b₀ * h) * h⁻¹ = b₀ by group]
      exact hb₀C
    rwa [E3.conjSubgroup_centralizer, hW1h] at h1'
  have hbC1 : b ∈ E3.cClos V 1 T := ⟨hbT, hbC⟩
  have hXcent : X ≤ centralizer ({b} : Set G) := by
    intro x hx
    have hxres : x ∈ twoResidual (X ⊔ T) := hXres hx
    have hxc : x ∈ centralizer (E3.cClos V 1 T : Set G) := hleC hxres
    rw [Subgroup.mem_centralizer_iff] at hxc ⊢
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    exact hxc b hbC1
  have hXN : X ≤ normalizer (conjSubgroup V h : Set G) :=
    hXcent.trans (centralizer_le_normalizer_conj h9.hyp7.2.2 h hbVh hb1)
  have hXMh : X ≤ conjSubgroup (normalizer (V : Set G)) h := by
    rw [E3.conjSubgroup_normalizer]
    exact hXN
  have hXbot : X = ⊥ := by
    have htriv := hXtriv h hhM hVhM
    rw [← inf_eq_left.2 hXMh]
    exact htriv
  exact hX1 hXbot

theorem exists_inf_sup_of_le_sup {K₀ : Subgroup G} (hXT : (X : Set G) * T = T * X)
    (hTK : T ≤ K₀) (hK : K₀ ≤ X ⊔ T) :
    (K₀ ⊓ X : Subgroup G) ⊔ T = K₀ ∧
      ((K₀ ⊓ X : Subgroup G) : Set G) * (T : Set G) = (T : Set G) * (K₀ ⊓ X : Subgroup G) := by
  have hmem := nineThirteenAux_mem_sup_iff hXT
  have hset : (K₀ : Set G) = (T : Set G) * (K₀ ⊓ X : Subgroup G) := by
    refine Set.Subset.antisymm ?_ ?_
    · intro k hk
      obtain ⟨t, ht, x, hx, htx⟩ := (hmem k).1 (hK hk)
      have hxK : x ∈ K₀ := by
        have ht' : t⁻¹ * k ∈ K₀ := K₀.mul_mem (K₀.inv_mem (hTK ht)) hk
        rwa [show t⁻¹ * k = x by rw [← htx]; group] at ht'
      exact Set.mem_mul.2 ⟨t, ht, x, ⟨hxK, hx⟩, htx⟩
    · rintro k ⟨t, ht, x, hx, rfl⟩
      change t * x ∈ K₀
      exact K₀.mul_mem (hTK ht) hx.1
  have hset' : (K₀ : Set G) = ((K₀ ⊓ X : Subgroup G) : Set G) * (T : Set G) := by
    refine Set.Subset.antisymm ?_ ?_
    · intro k hk
      have hkinv : k⁻¹ ∈ (T : Set G) * (K₀ ⊓ X : Subgroup G) := hset ▸ K₀.inv_mem hk
      obtain ⟨t, ht, x, hx, htx⟩ := Set.mem_mul.1 hkinv
      change t * x = k⁻¹ at htx
      have hk_eq : k = x⁻¹ * t⁻¹ := by
        rw [← inv_inv k, ← htx]
        group
      exact Set.mem_mul.2 ⟨x⁻¹, ⟨K₀.inv_mem hx.1, X.inv_mem hx.2⟩, t⁻¹, T.inv_mem ht,
        hk_eq.symm⟩
    · rintro k ⟨x, hx, t, ht, rfl⟩
      change x * t ∈ K₀
      exact K₀.mul_mem hx.1 (hTK ht)
  refine ⟨?_, ?_⟩
  · apply le_antisymm
    · exact sup_le inf_le_left hTK
    · intro k hk
      have hk' : k ∈ (T : Set G) * (K₀ ⊓ X : Subgroup G) := by
        rw [← hset]
        exact hk
      obtain ⟨t, ht, x, hx, htx⟩ := Set.mem_mul.1 hk'
      change t * x = k at htx
      rw [← htx, sup_comm]
      exact Subgroup.mul_mem_sup ht hx
  · rw [← hset', hset]

end CFSG.LocalAnalysis.WeakClosure81
