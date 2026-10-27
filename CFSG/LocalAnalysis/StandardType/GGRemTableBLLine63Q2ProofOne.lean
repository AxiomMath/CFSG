module

public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLine63Q2ProofRed
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLine63H5Assembly
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLine63H5Class
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLineL2Remainder
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLineUCoverOdd

public section

namespace CFSG.StandardType.Line63.H5

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.SectionRank.OddCover CFSG.StandardType.LineU CFSG.Assembly CFSG.StandardType

section Abstract

variable {K : Type} [Field K] {n : ℕ} {G : Type} [Group G]

theorem false_of_injective_cover_of_not_nine [Finite K] [Finite G] (hKd : UnitaryFieldData 2 n K)
    (hpq : 3 ∣ 2 ^ n + 1) (h9 : ¬ 9 ∣ 2 ^ n + 1) (φ : ↥(unitarySU 2 n K 6) →* G)
    (hφ : Function.Injective φ) {B : Subgroup G} (hB : CFSG.Open.IsElemAbelian 3 B)
    (hcyc : ∀ S : Subgroup G, S ≤ Subgroup.centralizer ((φ.range : Subgroup G) : Set G) →
      IsPGroup 3 S → IsCyclic S)
    {x : G} (hxB : x ∈ B) (hx1 : x ≠ 1) (hxC : ∀ s, x * φ s = φ s * x)
    {a b₀ : G} (haB : a ∈ B) (hbB : b₀ ∈ B) {Ma Mb : GL (Fin 6) K}
    (ha : ActsAs φ a Ma) (hb : ActsAs φ b₀ Mb)
    (hbin : ∃ (t : Kˣ) (s₀ : ↥(unitarySU 2 n K 6)),
      Mb = GeneralLinearGroup.scalar (Fin 6) t * (s₀ : GL (Fin 6) K))
    (hne : Ma * Mb ≠ Mb * Ma) : False := by
  classical
  obtain ⟨t, s₀, hMb⟩ := hbin
  subst hMb
  have hcC0 := commute_of_actsAs_inner hb
  set l : G := φ s₀ with hl
  set c : G := l⁻¹ * b₀ with hc
  have hcC : ∀ s, c * φ s = φ s * c := fun s => hcC0 s
  have hb0 : b₀ = l * c := by rw [hc]; group
  have hlc : Commute l c := (hcC s₀).symm
  have hb03 : b₀ ^ 3 = 1 := hB.2 b₀ hbB
  have hlc3 : l ^ 3 * c ^ 3 = 1 := by
    rw [← hlc.mul_pow, ← hb0]
    exact hb03
  have hc3l : c ^ 3 = (l ^ 3)⁻¹ := eq_inv_of_mul_eq_one_right hlc3
  have hcent : ∀ s : ↥(unitarySU 2 n K 6), s₀ ^ 3 * s = s * s₀ ^ 3 := by
    intro s
    apply hφ
    rw [map_mul, map_mul, map_pow, ← hl]
    have h1 : l ^ 3 = (c ^ 3)⁻¹ := by rw [hc3l, inv_inv]
    rw [h1]
    have h2 : Commute (c ^ 3) (φ s) := (Commute.pow_left (hcC s) 3)
    exact h2.inv_left.eq
  have hscal : ((s₀ ^ 3 : ↥(unitarySU 2 n K 6)) : GL (Fin 6) K) ∈ LargeEvenScalars (Fin 6) K :=
    TableBUE.mem_scalars_of_commute hKd Nat.prime_three hpq fun g hg => by
      exact congrArg Subtype.val (hcent ⟨g, hg⟩)
  rw [largeEvenScalars_def] at hscal
  obtain ⟨w, hw⟩ := hscal
  have hw3 : w ^ 3 = 1 :=
    pow_three_eq_one_of_scalar_mem_unitarySU hKd hpq (hw ▸ (s₀ ^ 3).2)
  by_cases hw1 : w = 1
  · have hs3 : s₀ ^ 3 = 1 := by
      apply Subtype.ext
      rw [← hw, hw1, map_one]
      rfl
    have hl3 : l ^ 3 = 1 := by rw [hl, ← map_pow, hs3, map_one]
    have hc3 : c ^ 3 = 1 := by rw [hc3l, hl3]; group
    have hxc : Commute x c := by
      have h1 : Commute x l := hxC s₀
      have h2 : Commute x b₀ := (CFSG.StandardType.TableB.IsElemAbelian.comm hB hxB hbB)
      rw [hc]
      exact h1.inv_right.mul_right h2
    have hxcen : x ∈ Subgroup.centralizer ((φ.range : Subgroup G) : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨s, rfl⟩
      exact (hxC s).symm
    have hccen : c ∈ Subgroup.centralizer ((φ.range : Subgroup G) : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨s, rfl⟩
      exact (hcC s).symm
    set S : Subgroup G := Subgroup.zpowers x ⊔ Subgroup.zpowers c with hS
    have hx3 : x ^ 3 = 1 := hB.2 x hxB
    have hSab : CFSG.Open.IsElemAbelian 3 S :=
      CFSG.StandardType.TableB.isElemAbelian_sup (isElemAbelian_zpowers hx3)
        (isElemAbelian_zpowers hc3) (fun a ha b hb => by
          obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
          obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
          exact ((hxc.zpow_left i).zpow_right j).eq)
    have hSp : IsPGroup 3 S := fun g => ⟨1, Subtype.ext (by simpa using hSab.2 g g.2)⟩
    have hSle : S ≤ Subgroup.centralizer ((φ.range : Subgroup G) : Set G) :=
      sup_le ((Subgroup.zpowers_le).mpr hxcen) ((Subgroup.zpowers_le).mpr hccen)
    have hSc : IsCyclic S := hcyc S hSle hSp
    have hcx : c ∈ Subgroup.zpowers x :=
      mem_zpowers_of_isCyclic_of_pow_three hSc (le_sup_left (a := Subgroup.zpowers x)
        (b := Subgroup.zpowers c) (Subgroup.mem_zpowers x)) (le_sup_right
        (a := Subgroup.zpowers x) (b := Subgroup.zpowers c) (Subgroup.mem_zpowers c)) hx3 hx1 hc3
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hcx
    have hax : Commute a x := CFSG.StandardType.TableB.IsElemAbelian.comm hB haB hxB
    have hac : Commute a c := by rw [← hj]; exact hax.zpow_right j
    have hab : Commute a b₀ := CFSG.StandardType.TableB.IsElemAbelian.comm hB haB hbB
    have hal : Commute a l := by
      have : l = b₀ * c⁻¹ := by rw [hb0]; group
      rw [this]
      exact hab.mul_right hac.inv_right
    obtain ⟨hMa, hactA⟩ := ha
    have h1 := hactA s₀
    rw [← hl, hal.eq, mul_inv_cancel_right] at h1
    have h2 : conjN Ma hMa s₀ = s₀ := hφ h1.symm
    have h3 := congrArg Subtype.val h2
    rw [coe_conjN] at h3
    apply hne
    have h4 : Ma * (s₀ : GL (Fin 6) K) = (s₀ : GL (Fin 6) K) * Ma := by
      calc Ma * (s₀ : GL (Fin 6) K) = Ma * (s₀ : GL (Fin 6) K) * Ma⁻¹ * Ma := by group
        _ = (s₀ : GL (Fin 6) K) * Ma := by rw [h3]
    calc Ma * (GeneralLinearGroup.scalar (Fin 6) t * (s₀ : GL (Fin 6) K))
        = GeneralLinearGroup.scalar (Fin 6) t * (Ma * (s₀ : GL (Fin 6) K)) := by
          rw [← mul_assoc, ← mul_assoc, ((commute_scalar t Ma).eq)]
      _ = GeneralLinearGroup.scalar (Fin 6) t * ((s₀ : GL (Fin 6) K) * Ma) := by rw [h4]
      _ = (GeneralLinearGroup.scalar (Fin 6) t * (s₀ : GL (Fin 6) K)) * Ma := by
          rw [mul_assoc]
  · have hs₀3 : s₀ ^ 3 = scalarSU hKd hpq hw3 := by
      apply Subtype.ext
      show ((s₀ ^ 3 : ↥(unitarySU 2 n K 6)) : GL (Fin 6) K) = diagHom 6 (fun _ => w)
      rw [← hw, diagHom_const_eq_scalar]
    exact false_of_pow_three_eq_scalar hKd hpq h9 hw3 hw1 s₀ hs₀3

theorem false_of_injective_cover_class_of_not_nine [Finite K] [Finite G]
    (hKd : UnitaryFieldData 2 n K) (hpq : 3 ∣ 2 ^ n + 1) (h9 : ¬ 9 ∣ 2 ^ n + 1)
    (φ : ↥(unitarySU 2 n K 6) →* G) (hφ : Function.Injective φ) {B : Subgroup G}
    (hB : CFSG.Open.IsElemAbelian 3 B) (hBcard : Nat.card B = 3 ^ 4)
    (hSC : ∀ g ∈ Subgroup.centralizer (B : Set G), g ^ 3 = 1 → g ∈ B)
    (hcyc : ∀ S : Subgroup G, S ≤ Subgroup.centralizer ((φ.range : Subgroup G) : Set G) →
      IsPGroup 3 S → IsCyclic S)
    {x : G} (hxB : x ∈ B) (hx1 : x ≠ 1) (hxC : ∀ s, x * φ s = φ s * x)
    (hact : ∀ b ∈ B, ∃ M, M ∈ LargeEvenGUSet (Fin 6) K (2 ^ n) ∧ ActsAs φ b M) : False := by
  obtain ⟨a, haB, b₀, hbB, Ma, Mb, ha, hb, hin, hne⟩ :=
    exists_noncomm_pair hKd hpq φ hφ hB hBcard hSC hcyc hxB hx1 hxC hact
  exact false_of_injective_cover_of_not_nine hKd hpq h9 φ hφ hB hcyc hxB hx1 hxC haB hbB ha hb
    hin hne

theorem injective_of_scalar_ne_one [Finite K] (hKd : UnitaryFieldData 2 n K)
    (hpq : 3 ∣ 2 ^ n + 1) {Gr : Type} [Group Gr] (φ : ↥(unitarySU 2 n K 6) →* Gr)
    (hker : ∀ s, φ s = 1 → LargeEvenProjMk (unitarySU 2 n K 6) s = 1)
    {s₀ : ↥(unitarySU 2 n K 6)} (hs₀ : LargeEvenProjMk (unitarySU 2 n K 6) s₀ = 1)
    (hs₁ : φ s₀ ≠ 1) : Function.Injective φ := by
  classical
  rw [injective_iff_map_eq_one]
  intro t ht
  by_contra ht1
  have ht' : LargeEvenProjMk (unitarySU 2 n K 6) t = 1 := hker t ht
  obtain ⟨c₁, hc₁3, hc₁⟩ := exists_scalar_of_proj_eq_one hKd hpq ht'
  obtain ⟨c₀, hc₀3, hc₀⟩ := exists_scalar_of_proj_eq_one hKd hpq hs₀
  have hc₁1 : c₁ ≠ 1 := by
    rintro rfl
    apply ht1
    apply Subtype.ext
    rw [hc₁, map_one]
    rfl
  have hc₀1 : c₀ ≠ 1 := by
    rintro rfl
    apply hs₁
    have : s₀ = 1 := Subtype.ext (by rw [hc₀, map_one]; rfl)
    rw [this, map_one]
  haveI : IsCyclic (⊤ : Subgroup Kˣ) := (Subgroup.topEquiv (G := Kˣ)).isCyclic.mpr inferInstance
  have hmem : c₀ ∈ Subgroup.zpowers c₁ :=
    mem_zpowers_of_isCyclic_of_pow_three (S := (⊤ : Subgroup Kˣ)) inferInstance trivial trivial
      hc₁3 hc₁1 hc₀3
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
  apply hs₁
  have h1 : s₀ = t ^ k := by
    apply Subtype.ext
    rw [hc₀, ← hk, Subgroup.coe_zpow, hc₁, ← map_zpow]
  rw [h1, map_zpow, ht, _root_.one_zpow]

end Abstract

section Transfer

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {Bs : Subgroup G}

theorem mem_center_of_mem_twoCenter {l : ↥L} (h : (l : G) ∈ twoCenter L) :
    l ∈ Subgroup.center ↥L := by
  rw [Subgroup.mem_center_iff]
  intro g
  exact Subtype.ext (h.2.1 g g.2).symm

@[expose] def redMkB (hBN : Bs ≤ Subgroup.normalizer (L : Set G)) : ↥Bs →* RedGrp L :=
  (redMk L).comp (Subgroup.inclusion hBN)

theorem redMkB_injective (hBN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hBs : CFSG.Open.IsElemAbelian 3 Bs) : Function.Injective (redMkB hBN) := by
  rw [injective_iff_map_eq_one]
  intro b hb
  have h1 : (b : G) ∈ twoCenter L := (redMk_eq_one_iff L (Subgroup.inclusion hBN b)).mp hb
  have h3 : (b : G) ^ 3 = 1 := hBs.2 b b.2
  exact Subtype.ext (eq_one_of_cube (isPGroup_twoCenter L) h1 h3)

theorem isElemAbelian_redB (hBN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hBs : CFSG.Open.IsElemAbelian 3 Bs) :
    CFSG.Open.IsElemAbelian 3 (redMkB hBN).range := by
  refine ⟨⟨⟨?_⟩⟩, ?_⟩
  · rintro ⟨_, a, rfl⟩ ⟨_, b, rfl⟩
    apply Subtype.ext
    show redMkB hBN a * redMkB hBN b = redMkB hBN b * redMkB hBN a
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (CFSG.StandardType.TableB.IsElemAbelian.comm hBs a.2 b.2)
  · rintro _ ⟨b, rfl⟩
    rw [← map_pow]
    have : b ^ 3 = 1 := Subtype.ext (by simpa using hBs.2 b b.2)
    rw [this, map_one]

theorem card_redB (hBN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hBs : CFSG.Open.IsElemAbelian 3 Bs) :
    Nat.card (redMkB hBN).range = Nat.card Bs :=
  (Nat.card_congr (MonoidHom.ofInjective (redMkB_injective hBN hBs)).toEquiv).symm

theorem redSC (hBN : Bs ≤ Subgroup.normalizer (L : Set G)) (hBs : CFSG.Open.IsElemAbelian 3 Bs)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs) :
    ∀ g ∈ Subgroup.centralizer (((redMkB hBN).range : Subgroup (RedGrp L)) : Set (RedGrp L)),
      g ^ 3 = 1 → g ∈ (redMkB hBN).range := by
  classical
  intro gbar hgbarc hgbar3
  set Bbar : Subgroup (RedGrp L) := (redMkB hBN).range with hBbar
  have hBbarab : CFSG.Open.IsElemAbelian 3 Bbar := isElemAbelian_redB hBN hBs
  have hcomm : ∀ a ∈ Bbar, ∀ c ∈ Subgroup.zpowers gbar, a * c = c * a := by
    intro a ha c hc
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc
    exact ((show Commute a gbar from Subgroup.mem_centralizer_iff.mp hgbarc a ha).zpow_right k).eq
  set Ybar : Subgroup (RedGrp L) := Bbar ⊔ Subgroup.zpowers gbar with hYbar
  have hYbarab : CFSG.Open.IsElemAbelian 3 Ybar :=
    CFSG.StandardType.TableB.isElemAbelian_sup hBbarab (isElemAbelian_zpowers hgbar3) hcomm
  have hYbarp : IsPGroup 3 Ybar := isPGroup_three_of_isElemAbelian hYbarab
  have hYbarr : Ybar ≤ (redMk L).range := fun y _ => QuotientGroup.mk'_surjective _ y
  have hBH : IsPGroup 3 (Subgroup.inclusion hBN).range :=
    (isPGroup_three_of_isElemAbelian hBs).of_surjective (Subgroup.inclusion hBN).rangeRestrict
      (Subgroup.inclusion hBN).rangeRestrict_surjective
  obtain ⟨S, hBS, hSp, hSmap, hSinj⟩ := exists_sylow_lift (redMk L) (isPGroup_ker_redMk L) hYbarp
    hYbarr (B := (Subgroup.inclusion hBN).range) hBH (by
      rintro _ ⟨_, ⟨b, rfl⟩, rfl⟩
      exact Subgroup.mem_sup_left ⟨b, rfl⟩)
  have hSY : ∀ s ∈ S, redMk L s ∈ Ybar := fun s hs => by rw [← hSmap]; exact ⟨s, hs, rfl⟩
  have hScomm : ∀ s ∈ S, ∀ t ∈ S, s * t = t * s := by
    intro s hs t ht
    have hc : redMk L s * redMk L t = redMk L t * redMk L s :=
      CFSG.StandardType.TableB.IsElemAbelian.comm hYbarab (hSY s hs) (hSY t ht)
    have h1 : s * t * (t * s)⁻¹ = 1 := hSinj _
      (S.mul_mem (S.mul_mem hs ht) (S.inv_mem (S.mul_mem ht hs))) (by
        rw [map_mul, map_mul, map_inv, map_mul, hc]
        group)
    exact mul_inv_eq_one.mp h1
  have hSexp : ∀ s ∈ S, s ^ 3 = 1 := by
    intro s hs
    refine hSinj _ (S.pow_mem hs 3) ?_
    rw [map_pow]
    exact hYbarab.2 _ (hSY s hs)
  have hgbarY : gbar ∈ Ybar := Subgroup.mem_sup_right (Subgroup.mem_zpowers gbar)
  rw [← hSmap] at hgbarY
  obtain ⟨g, hgS, rfl⟩ := hgbarY
  have hgc : (g : G) ∈ Subgroup.centralizer (Bs : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    have hbS : Subgroup.inclusion hBN ⟨b, hb⟩ ∈ S := hBS ⟨⟨b, hb⟩, rfl⟩
    exact congrArg Subtype.val (hScomm _ hbS g hgS)
  have hg3 : (g : G) ^ 3 = 1 := by simpa using congrArg Subtype.val (hSexp g hgS)
  have hgB : (g : G) ∈ Bs := hSC _ hgc hg3
  exact ⟨⟨g, hgB⟩, rfl⟩

theorem noTransvection_red (hBN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hBs : CFSG.Open.IsElemAbelian 3 Bs)
    (hNT : CFSG.StandardType.GGNoTransvection 3 Bs) :
    CFSG.StandardType.GGNoTransvection 3 (redMkB hBN).range := by
  classical
  let N : Subgroup G := Subgroup.normalizer (L : Set G)
  let B' : Subgroup ↥N := Bs.subgroupOf N
  let Z : Subgroup ↥N := (twoCenter L).subgroupOf N
  haveI : Z.Normal := twoCenter_normal (L := L)
  have hBsp : IsPGroup 3 B' :=
    (CFSG.StandardType.isPGroup_of_isElemAbelian hBs).comap_subtype
  have hodd : ¬ 3 ∣ Nat.card Z := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hZ2 : IsPGroup 2 Z := (isPGroup_twoCenter L).comap_subtype
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hZ2
    rw [hk]
    intro h
    exact (by norm_num : ¬ (3 : ℕ) ∣ 2) (Nat.prime_three.dvd_of_dvd_pow h)
  have hNT' : CFSG.StandardType.GGNoTransvection 3 B' :=
    CFSG.StandardType.noTransvection_subgroupOf (H := N) hBN hNT
  have h := CFSG.StandardType.noTransvection_map_mk'_of_coprime
    (G := ↥N) (N := Z) (p := 3) hodd hBsp hNT'
  have hBeq : B'.map (QuotientGroup.mk' Z) = (redMkB hBN).range := by
    ext q
    constructor
    · rintro ⟨b, hb, rfl⟩
      exact ⟨⟨(b : G), Subgroup.mem_subgroupOf.mp hb⟩, rfl⟩
    · rintro ⟨b, rfl⟩
      exact ⟨⟨(b : G), hBN b.2⟩, Subgroup.mem_subgroupOf.mpr b.2, rfl⟩
  rwa [hBeq] at h

theorem redMk_conj (n : ↥(Subgroup.normalizer (L : Set G))) (l : ↥L) :
    redMk L n * redMkL L l * (redMk L n)⁻¹ = redMkL L (L.normalizerMonoidHom n l) := by
  have e0 : Subgroup.inclusion Subgroup.le_normalizer (L.normalizerMonoidHom n l) =
      n * Subgroup.inclusion Subgroup.le_normalizer l * n⁻¹ := Subtype.ext rfl
  show _ = redMk L (Subgroup.inclusion Subgroup.le_normalizer (L.normalizerMonoidHom n l))
  rw [e0, map_mul, map_mul, map_inv]
  rfl

theorem redCyc {R : Type} [Group R] (θ : L ⧸ Subgroup.center L ≃* R) (hL : commutator L = ⊤)
    (hcyc : ∀ S : Subgroup G, S ≤ Subgroup.centralizer (L : Set G) → IsPGroup 3 S → IsCyclic S)
    {X : Type*} [Group X] {φ : X →* RedGrp L} (hrange : ∀ l : ↥L, ∃ x, φ x = redMkL L l) :
    ∀ S : Subgroup (RedGrp L), S ≤ Subgroup.centralizer ((φ.range : Subgroup (RedGrp L)) :
      Set (RedGrp L)) → IsPGroup 3 S → IsCyclic S := by
  classical
  intro Sbar hSc hSp
  have hr : Sbar ≤ (redMk L).range := fun y _ => QuotientGroup.mk'_surjective _ y
  obtain ⟨S, -, hS3, hSmap, -⟩ := exists_sylow_lift (redMk L) (isPGroup_ker_redMk L) hSp hr
    (B := ⊥) IsPGroup.of_bot (by simp)
  have hSb : ∀ s ∈ S, redMk L s ∈ Sbar := fun s hs => by rw [← hSmap]; exact ⟨s, hs, rfl⟩
  have hcentr : ∀ s ∈ S, (s : G) ∈ Subgroup.centralizer (L : Set G) := by
    intro s hs
    have hg1 : ggLAut L θ s = 1 := by
      ext r
      obtain ⟨q, rfl⟩ := θ.surjective r
      induction q using QuotientGroup.induction_on with
      | H l =>
        rw [ggLAut_apply, MulAut.one_apply]
        refine congrArg θ (QuotientGroup.eq.mpr ?_)
        refine mem_center_of_mem_twoCenter ((redMkL_eq_one_iff L _).mp ?_)
        have h1 : redMkL L (L.normalizerMonoidHom s l) = redMkL L l := by
          obtain ⟨x, hx⟩ := hrange l
          have hcomm : φ x * redMk L s = redMk L s * φ x :=
            Subgroup.mem_centralizer_iff.mp (hSc (hSb s hs)) (φ x) ⟨x, rfl⟩
          rw [hx] at hcomm
          rw [← redMk_conj, ← hcomm]
          group
        rw [map_mul, map_inv, h1, inv_mul_cancel]
    exact mem_centralizer_of_ggLAut_eq_one L θ hL (g := s) hg1
  set S' : Subgroup G := S.map (Subgroup.normalizer (L : Set G)).subtype with hS'
  have hS'le : S' ≤ Subgroup.centralizer (L : Set G) := by
    rintro _ ⟨s, hs, rfl⟩
    exact hcentr s hs
  have hS'cyc : IsCyclic S' := hcyc S' hS'le (hS3.map _)
  have hScyc : IsCyclic S :=
    (Subgroup.equivMapOfInjective S _ Subtype.coe_injective).isCyclic.mpr hS'cyc
  let f : ↥S →* ↥Sbar := ((redMk L).comp S.subtype).codRestrict Sbar (fun s => hSb s s.2)
  have hf : Function.Surjective f := by
    rintro ⟨y, hy⟩
    rw [← hSmap] at hy
    obtain ⟨s, hs, rfl⟩ := hy
    exact ⟨⟨s, hs⟩, Subtype.ext rfl⟩
  haveI := hScyc
  exact isCyclic_of_surjective f hf

end Transfer

section StepOne

variable {K : Type} [Field K] [Finite K] {G : Type} [Group G] [Finite G] {L : Subgroup G}
  {Bs : Subgroup G}

theorem redActsAs (hcov : Line63.UnitaryCoverOddAt 1 6 K)
    (hKd : UnitaryFieldData 2 1 K)
    (θ : L ⧸ Subgroup.center L ≃* LargeEvenProj (unitarySU 2 1 K 6))
    {φ : ↥(unitarySU 2 1 K 6) →* RedGrp L} (hφ1 : ∀ s, φ s ∈ (redMkL L).range)
    (hφ3 : ∀ (s : ↥(unitarySU 2 1 K 6)) (l : ↥L), φ s = redMkL L l →
      ggQuotHom θ l = LargeEvenProjMk (unitarySU 2 1 K 6) s)
    (hBN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hBI : ∀ b ∈ Bs, ∃ φ ∈ LargeEvenMatConjImage (LargeEvenProjMk (unitarySU 2 1 K 6))
      (LargeEvenGUSet (Fin 6) K (2 ^ 1)),
      LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ) (b : ↥Bs) :
    ∃ M ∈ LargeEvenGUSet (Fin 6) K (2 ^ 1), ActsAs φ (redMkB hBN b) M := by
  classical
  obtain ⟨A, hA, hgraph⟩ := ggLAut_mem_of_induces L θ hBN hBI b.2
  have hAN : A ∈ Subgroup.normalizer (unitarySU 2 1 K 6 : Set (GL (Fin 6) K)) :=
    TableBUE.gu_subset_normalizer (d := 6) hKd hA
  refine ⟨A, hA, hAN, fun s => ?_⟩
  set nb : ↥(Subgroup.normalizer (L : Set G)) := ⟨(b : G), hBN b.2⟩ with hnb
  have hnb' : redMkB hBN b = redMk L nb := rfl
  rw [hnb']
  set φ₀ : ↥(unitarySU 2 1 K 6) →* ↥(redMkL L).range := φ.codRestrict _ hφ1 with hφ₀
  set f₁ : ↥(unitarySU 2 1 K 6) →* ↥(redMkL L).range :=
    (MulAut.conjNormal (redMk L nb)).toMonoidHom.comp φ₀ with hf₁
  set f₂ : ↥(unitarySU 2 1 K 6) →* ↥(redMkL L).range := φ₀.comp (conjNHom A hAN) with hf₂
  have hf : f₁ = f₂ := by
    refine TypeA.eq_of_inv_mul_mem_center hcov.1 f₁ f₂ fun s' => ?_
    obtain ⟨l₁, hl₁⟩ := hφ1 s'
    obtain ⟨l₂, hl₂⟩ := hφ1 (conjN A hAN s')
    have hψ₁ := hφ3 s' l₁ hl₁.symm
    have hψ₂ := hφ3 (conjN A hAN s') l₂ hl₂.symm
    set z : ↥L := (L.normalizerMonoidHom nb l₁)⁻¹ * l₂ with hz
    have hzψ : ggQuotHom θ z = 1 := by
      have h1 : ggQuotHom θ (L.normalizerMonoidHom nb l₁) =
          ggLAut L θ nb (ggQuotHom θ l₁) := by
        rw [ggQuotHom_apply, ggQuotHom_apply, ggLAut_apply]
      have h2 : ggLAut L θ nb (LargeEvenProjMk (unitarySU 2 1 K 6) s') =
          LargeEvenProjMk (unitarySU 2 1 K 6) (conjN A hAN s') :=
        hgraph s' (conjN A hAN s') rfl
      rw [hz, map_mul, map_inv, h1, hψ₁, h2, hψ₂, inv_mul_cancel]
    have hzc : z ∈ Subgroup.center ↥L := by
      rw [← ker_ggQuotHom θ]
      exact hzψ
    have hval : (((f₁ s')⁻¹ * f₂ s' : ↥(redMkL L).range) : RedGrp L) = redMkL L z := by
      have e1 : ((f₁ s' : ↥(redMkL L).range) : RedGrp L) =
          redMkL L (L.normalizerMonoidHom nb l₁) := by
        rw [← redMk_conj, hl₁]
        simp [hf₁, hφ₀]
      have e2 : ((f₂ s' : ↥(redMkL L).range) : RedGrp L) = redMkL L l₂ := by
        rw [hl₂]
        simp [hf₂, hφ₀, coe_conjNHom]
      rw [Subgroup.coe_mul, Subgroup.coe_inv, e1, e2, hz, map_mul, map_inv]
    have hu : (f₁ s')⁻¹ * f₂ s' = (⟨redMkL L z, ⟨z, rfl⟩⟩ : ↥(redMkL L).range) :=
      Subtype.ext hval
    rw [hu, Subgroup.mem_center_iff]
    rintro ⟨y, l₃, rfl⟩
    apply Subtype.ext
    show redMkL L l₃ * redMkL L z = redMkL L z * redMkL L l₃
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hzc l₃]
  have h := congrArg (fun f : ↥(unitarySU 2 1 K 6) →* ↥(redMkL L).range =>
    ((f s : ↥(redMkL L).range) : RedGrp L)) hf
  simpa [hf₁, hf₂, hφ₀, coe_conjNHom] using h

end StepOne

section Main

theorem stepOne_two
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hcfg : GGConfig 3 B Bs x L D J) (hlt : Nat.card Bs < 3 ^ 5)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = (2 ^ 1) ^ 2) (hL : commutator L = ⊤)
    (θ : L ⧸ Subgroup.center L ≃* LargeEvenProj (unitarySU 2 1 K 6))
    (hBN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hBI : ∀ b ∈ Bs, ∃ φ ∈ LargeEvenMatConjImage (LargeEvenProjMk (unitarySU 2 1 K 6))
      (LargeEvenGUSet (Fin 6) K (2 ^ 1)),
      LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ)
    {z : G} (hzL : z ∈ L) (hzc : ∀ l ∈ L, z * l = l * z) (hz3 : z ^ 3 = 1) (hz1 : z ≠ 1) :
    False := by
  classical
  have hK4 : Nat.card K = 4 := by rw [hK]; norm_num
  have hKd : UnitaryFieldData 2 1 K := TableBU.unitaryFieldData_of_card hK (Nat.le_refl 1)
  have hpq : 3 ∣ 2 ^ 1 + 1 := by norm_num
  have h9 : ¬ 9 ∣ 2 ^ 1 + 1 := by norm_num
  have hcov := LineU.unitaryCoverOddAt_six_two K hK4
  obtain ⟨φ, hφ1, hφ2, hφ3⟩ := exists_redCover hcov hL θ
  obtain ⟨hp, hBs, hxBs, hLx, -⟩ := hcfg.tableB_facts
  obtain ⟨hcard, -⟩ := config_card_rank hcfg hlt
  have hS : LargeEvenSStar 3 B x L := hcfg.1.2.2.2.2.2.2.1
  have hx3 : x ^ 3 = 1 := hBs.2 x hxBs
  have hxC : ∀ l ∈ L, x * l = l * x := fun l hl =>
    (Subgroup.mem_centralizer_singleton_iff.mp (hLx hl)).symm
  set nx : ↥(Subgroup.normalizer (L : Set G)) := ⟨x, hBN hxBs⟩ with hnx
  have hker : ∀ s, φ s = 1 → LargeEvenProjMk (unitarySU 2 1 K 6) s = 1 := by
    intro s hs
    have h1 := hφ3 s 1 (by rw [hs, map_one])
    rw [← h1, map_one]
  obtain ⟨s₀, hs₀⟩ := hφ2 ⟨z, hzL⟩
  have hzcent : (⟨z, hzL⟩ : ↥L) ∈ Subgroup.center ↥L := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hzc g g.2).symm
  have hs₀p : LargeEvenProjMk (unitarySU 2 1 K 6) s₀ = 1 := by
    rw [← hφ3 s₀ ⟨z, hzL⟩ hs₀]
    rw [← ker_ggQuotHom θ] at hzcent
    exact hzcent
  have hs₀1 : φ s₀ ≠ 1 := by
    rw [hs₀]
    intro h
    exact hz1 (eq_one_of_cube (isPGroup_twoCenter L) ((redMkL_eq_one_iff L ⟨z, hzL⟩).mp h) hz3)
  have hinj : Function.Injective φ := injective_of_scalar_ne_one hKd hpq φ hker hs₀p hs₀1
  have hBbar : CFSG.Open.IsElemAbelian 3 (redMkB hBN).range := isElemAbelian_redB hBN hBs
  have hBcard : Nat.card (redMkB hBN).range = 3 ^ 4 := by rw [card_redB hBN hBs, hcard]
  have hSC := redSC hBN hBs (config_selfCent hcfg)
  have hcyc := redCyc θ hL (config_cyclic_sylow hcfg) hφ2
  have hxB : redMk L nx ∈ (redMkB hBN).range := ⟨⟨x, hxBs⟩, rfl⟩
  have hx1 : redMk L nx ≠ 1 := fun h =>
    hS.2.2.1 (eq_one_of_cube (isPGroup_twoCenter L) ((redMk_eq_one_iff L nx).mp h) hx3)
  have hxCφ : ∀ s, redMk L nx * φ s = φ s * redMk L nx := by
    intro s
    obtain ⟨l, hl⟩ := hφ1 s
    rw [← hl]
    have h1 : nx * Subgroup.inclusion Subgroup.le_normalizer l =
        Subgroup.inclusion Subgroup.le_normalizer l * nx := Subtype.ext (hxC l l.2)
    show redMk L nx * redMk L (Subgroup.inclusion _ l) =
      redMk L (Subgroup.inclusion _ l) * redMk L nx
    rw [← map_mul, ← map_mul, h1]
  have hact : ∀ b ∈ (redMkB hBN).range,
      ∃ M, M ∈ LargeEvenGUSet (Fin 6) K (2 ^ 1) ∧ ActsAs φ b M := by
    rintro _ ⟨b, rfl⟩
    obtain ⟨M, hM, hMA⟩ := redActsAs hcov hKd θ hφ1 hφ3 hBN hBI b
    exact ⟨M, hM, hMA⟩
  exact false_of_injective_cover_class_of_not_nine hKd hpq h9 φ hinj hBbar hBcard hSC hcyc hxB
    hx1 hxCφ hact

theorem line63StepOneQ2_holds :
    Line63StepOneQ2 := by
  intro G _ _ B Bs x L D J hcfg hlt K _ _ hK hL θ hBN hBI z hzL hzc hz3
  by_contra hz1
  exact stepOne_two hcfg hlt hK hL θ hBN hBI hzL hzc hz3 hz1

end Main



end CFSG.StandardType.Line63.H5

end
