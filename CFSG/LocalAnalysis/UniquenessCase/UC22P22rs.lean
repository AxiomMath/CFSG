module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S22b
import CFSG.LocalAnalysis.GLTheoremB.TwoGroupTools
import CFSG.LocalAnalysis.UniquenessCase.UC22Bridge3

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.LocalAnalysis.GLTheoremB (quotAutHom quotAutHom_mk)
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem uc22p22r_mem_uniqueSet_of_sp (D : Data G) {p : ℕ} (hp : p.Prime)
    (hsp : CFSG.RankThree.PartOne.IsStronglyPEmbedded p D.M) {X : Subgroup G} (hXM : X ≤ D.M)
    (hX : IsPGroup p X) (hX1 : X ≠ ⊥) : X ∈ uniqueSet D.M := by
  haveI : Fact p.Prime := ⟨hp⟩
  refine ⟨hXM, fun g hXg => ?_⟩
  by_cases hg : g ∈ D.M
  · exact Subgroup.mem_normalizer_iff_map_conj_eq.1 (Subgroup.le_normalizer hg)
  · exfalso
    apply hsp.2.2 g hg
    have hle : X ≤ D.M ⊓ D.M.map (MulAut.conj g).toMonoidHom := le_inf hXM hXg
    obtain ⟨k, hk⟩ := hX.exists_card_eq
    have hk0 : k ≠ 0 := by
      rintro rfl
      apply hX1
      exact Subgroup.eq_bot_of_card_eq X (by simpa using hk)
    have hdvd : p ∣ Nat.card X := by
      rw [hk]
      exact dvd_pow_self p hk0
    exact hdvd.trans (Subgroup.card_dvd_of_le hle)

section Lift

theorem uc22p22r_conj_eq_of_fix {M V : Subgroup G} (hVM : M ≤ normalizer (V : Set G)) {Vmod : Type}
    [AddCommGroup Vmod] [Module (ZMod 2) Vmod] (e : ↥V ≃* Multiplicative Vmod)
    (ρ : Representation (ZMod 2) (MBar M V) Vmod) (hc : ConjModule M V e ρ) (m : ↥M) (v : ↥V)
    (h : ρ (QuotientGroup.mk m) (Multiplicative.toAdd (e v)) = Multiplicative.toAdd (e v)) :
    (m : G) * v * (m : G)⁻¹ = v := by
  have hmem : (m : G) * v * (m : G)⁻¹ ∈ V :=
    (Subgroup.mem_normalizer_iff.1 (hVM m.2) v).1 v.2
  set w' : ↥V := ⟨(m : G) * v * (m : G)⁻¹, hmem⟩ with hw'
  have h1 := hc m v w' rfl
  rw [h, ofAdd_toAdd] at h1
  have h2 : w' = v := e.injective h1
  exact congrArg Subtype.val h2

theorem uc22p22r_quot_card_le {Q : Type} [Group Q] [Finite Q] {R S₀ : Subgroup Q} [hn : (S₀.subgroupOf R).Normal]
    {z : Q} {p : ℕ} (hp : p.Prime) (hzR : z ∈ R) (hzp : z ^ p = 1) (hRz : R = S₀ ⊔ Subgroup.zpowers z)
    (hS₀R : S₀ ≤ R) : Nat.card (↥R ⧸ S₀.subgroupOf R) ≤ p := by
  classical
  set φ := QuotientGroup.mk' (S₀.subgroupOf R) with hφ
  have hsurj : ∀ y : ↥R ⧸ S₀.subgroupOf R, y ∈ Subgroup.zpowers (φ ⟨z, hzR⟩) := by
    intro y
    obtain ⟨⟨r, hr⟩, rfl⟩ := QuotientGroup.mk'_surjective _ y
    have hr' : r ∈ ((S₀ ⊔ Subgroup.zpowers z : Subgroup Q) : Set Q) := hRz ▸ hr
    have hnorm : (Subgroup.zpowers z : Subgroup Q) ≤ normalizer (S₀ : Set Q) := by
      rw [Subgroup.zpowers_le]
      apply Subgroup.mem_normalizer_fintype
      intro y hy
      have h1 := hn.conj_mem ⟨y, hS₀R hy⟩ hy ⟨z, hzR⟩
      exact Subgroup.mem_subgroupOf.1 h1
    rw [Subgroup.coe_mul_of_right_le_normalizer_left S₀ (Subgroup.zpowers z) hnorm] at hr'
    obtain ⟨s, hs, x, hx, rfl⟩ := hr'
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    refine Subgroup.mem_zpowers_iff.2 ⟨k, ?_⟩
    rw [← map_zpow, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    rw [Subgroup.mem_subgroupOf]
    have e : ((⟨z, hzR⟩ : ↥R) ^ k : ↥R)⁻¹ * ⟨s * z ^ k, hr⟩ =
        (⟨z ^ k, R.zpow_mem hzR k⟩ : ↥R)⁻¹ * ⟨s, hS₀R hs⟩ * ⟨z ^ k, R.zpow_mem hzR k⟩ :=
      Subtype.ext (by simp [mul_assoc])
    rw [e]
    have h1 := Subgroup.mem_subgroupOf.1 (hn.conj_mem ⟨s, hS₀R hs⟩ hs (⟨z ^ k, R.zpow_mem hzR k⟩ : ↥R)⁻¹)
    simpa using h1
  have hle : Nat.card (↥R ⧸ S₀.subgroupOf R) ≤ Nat.card (Subgroup.zpowers (φ ⟨z, hzR⟩)) := by
    have : (⊤ : Subgroup (↥R ⧸ S₀.subgroupOf R)) ≤ Subgroup.zpowers (φ ⟨z, hzR⟩) := fun y _ => hsurj y
    calc Nat.card (↥R ⧸ S₀.subgroupOf R) = Nat.card (⊤ : Subgroup (↥R ⧸ S₀.subgroupOf R)) :=
          (Nat.card_congr Subgroup.topEquiv.toEquiv).symm
      _ ≤ _ := Subgroup.card_le_of_le this
  refine hle.trans ?_
  rw [Nat.card_zpowers]
  refine Nat.le_of_dvd hp.pos (orderOf_dvd_of_pow_eq_one ?_)
  rw [← map_pow]
  have : (⟨z, hzR⟩ : ↥R) ^ p = 1 := Subtype.ext (by simpa using hzp)
  rw [this, map_one]

theorem uc22p22r_inf_eq_bot_of_coprime {Q : Type} [Group Q] [Finite Q] {A B : Subgroup Q} {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hA : IsPGroup 2 A) (hB : IsPGroup p B) : A ⊓ B = ⊥ := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine Subgroup.eq_bot_of_card_eq _ ?_
  obtain ⟨i, hi⟩ := (hA.to_le (inf_le_left : A ⊓ B ≤ A)).exists_card_eq
  obtain ⟨j, hj⟩ := (hB.to_le (inf_le_right : A ⊓ B ≤ B)).exists_card_eq
  rw [hi] at hj ⊢
  rcases i with _ | i
  · simp
  · exfalso
    have h2 : 2 ∣ p ^ j := hj ▸ dvd_pow_self 2 (Nat.succ_ne_zero i)
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1 (Nat.prime_two.dvd_of_dvd_pow h2)).symm

theorem uc22p22r_card_pSubgroup_le {Q : Type} [Group Q] [Finite Q] {R S₀ : Subgroup Q}
    [hn : (S₀.subgroupOf R).Normal] (hS₀R : S₀ ≤ R) (hS₀2 : IsPGroup 2 S₀) {z : Q} {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hzR : z ∈ R) (hzp : z ^ p = 1) (hRz : R = S₀ ⊔ Subgroup.zpowers z) {P' : Subgroup Q}
    (hP'R : P' ≤ R) (hP'p : IsPGroup p P') : Nat.card P' ≤ p := by
  classical
  set φ := (QuotientGroup.mk' (S₀.subgroupOf R)).comp (Subgroup.inclusion hP'R) with hφ
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have h1 : (Subgroup.inclusion hP'R x) ∈ S₀.subgroupOf R := (QuotientGroup.eq_one_iff _).1 hx
    have h2 : (x : Q) ∈ S₀ ⊓ P' := ⟨h1, x.2⟩
    rw [uc22p22r_inf_eq_bot_of_coprime hp hp2 hS₀2 hP'p, Subgroup.mem_bot] at h2
    exact Subtype.ext h2
  have h1 : Nat.card P' ≤ Nat.card (↥R ⧸ S₀.subgroupOf R) := Nat.card_le_card_of_injective φ hinj
  exact h1.trans (uc22p22r_quot_card_le hp hzR hzp hRz hS₀R)

theorem uc22p22r_dvd_orderOf_quot {Q : Type} [Group Q] [Finite Q] {R S₀ : Subgroup Q}
    [hn : (S₀.subgroupOf R).Normal] (hS₀2 : IsPGroup 2 S₀) {z : Q} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hzR : z ∈ R) (hzo : orderOf z = p) {x : Q} (hxR : x ∈ R) (hxz : x⁻¹ * z ∈ S₀) : p ∣ orderOf x := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  set φ := QuotientGroup.mk' (S₀.subgroupOf R) with hφ
  have heq : φ ⟨x, hxR⟩ = φ ⟨z, hzR⟩ := by
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    simpa using hxz
  have hz1 : φ ⟨z, hzR⟩ ≠ 1 := by
    intro h
    have hzS : z ∈ S₀ := by
      have := (QuotientGroup.eq_one_iff _).1 h
      exact this
    obtain ⟨k, hk⟩ := hS₀2 ⟨z, hzS⟩
    have hk' : z ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hdvd : p ∣ 2 ^ k := hzo ▸ orderOf_dvd_of_pow_eq_one hk'
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow hdvd))
  have hzp : (φ ⟨z, hzR⟩) ^ p = 1 := by
    rw [← map_pow]
    have : (⟨z, hzR⟩ : ↥R) ^ p = 1 := Subtype.ext (by simpa [← hzo] using pow_orderOf_eq_one z)
    rw [this, map_one]
  have hord : orderOf (φ ⟨z, hzR⟩) = p := orderOf_eq_prime hzp hz1
  have h1 : orderOf (φ ⟨x, hxR⟩) ∣ orderOf (⟨x, hxR⟩ : ↥R) := orderOf_map_dvd φ _
  rw [heq, hord, Subgroup.orderOf_mk] at h1
  exact h1

theorem uc22p22r_set_mul_of_le {H K : Subgroup G} (h : H ≤ K) : (H : Set G) * (K : Set G) = K := by
  ext x
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact K.mul_mem (h ha) hb
  · intro hx
    exact ⟨1, H.one_mem, x, hx, one_mul x⟩

theorem uc22p22r_mul_set_of_le {H K : Subgroup G} (h : H ≤ K) : (K : Set G) * (H : Set G) = K := by
  ext x
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact K.mul_mem ha (h hb)
  · intro hx
    exact ⟨x, hx, 1, H.one_mem, mul_one x⟩

theorem uc22p22r_lift {M V T : Subgroup G} (hVM : M ≤ normalizer (V : Set G))
    (hTM : CFSG.ABGLocalTools.IsSylowOf 2 T M) {Vmod : Type} [AddCommGroup Vmod] [Module (ZMod 2) Vmod]
    (e : ↥V ≃* Multiplicative Vmod) (ρ : Representation (ZMod 2) (MBar M V) Vmod) (hc : ConjModule M V e ρ)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hrk : CFSG.Open.pRank p (M ⊓ centralizer (V : Set G)) ≤ 1)
    {R : Subgroup (MBar M V)} (hRT : mbarImage M V T ≤ normalizer (R : Set (MBar M V)))
    (hRn : ((R ⊓ mbarImage M V T).subgroupOf R).Normal) {z : MBar M V} (hzR : z ∈ R) (hzo : orderOf z = p)
    (hRz : R = (R ⊓ mbarImage M V T) ⊔ Subgroup.zpowers z) {w : Vmod} (hw : w ≠ 0)
    (hwfix : ∀ r ∈ R ⊔ mbarImage M V T, ρ r w = w) :
    ∃ v ∈ V, v ≠ 1 ∧ (∀ s ∈ T, s * v = v * s) ∧ ∃ A : Subgroup G, A ≤ M ∧
      A ≤ centralizer ({v} : Set G) ∧ A ≠ ⊥ ∧ IsPGroup p A ∧ (∀ a ∈ A, a ^ p = 1) ∧
      (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) ∧ Permutes A T ∧ CFSG.Open.pRank p A ≤ 2 := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π : ↥M →* MBar M V := QuotientGroup.mk' (kerAct M V).normalCore with hπdef
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  set Tb := mbarImage M V T with hTb
  set S₀ := R ⊓ Tb with hS₀
  have hmemTb : ∀ m : ↥M, (m : G) ∈ T → π m ∈ Tb := fun m hm => ⟨m, hm, rfl⟩
  have hTb2 : IsPGroup 2 Tb := by
    have h1 : IsPGroup 2 (T.subgroupOf M) := hTM.isPGroup.comap_subtype
    exact h1.map π
  have hS₀2 : IsPGroup 2 S₀ := hTb2.to_le inf_le_right
  set v' : ↥V := e.symm (Multiplicative.ofAdd w) with hv'
  have hev : Multiplicative.toAdd (e v') = w := by simp [hv']
  have hfix : ∀ m : ↥M, π m ∈ R ⊔ Tb → (m : G) * v' * (m : G)⁻¹ = v' := fun m hm =>
    uc22p22r_conj_eq_of_fix hVM e ρ hc m v' (by rw [hev]; exact hwfix _ hm)
  have hv1 : (v' : G) ≠ 1 := by
    intro h
    apply hw
    have : v' = 1 := Subtype.ext h
    rw [← hev, this, map_one, toAdd_one]
  have hcomm_of : ∀ g : G, g * v' * g⁻¹ = v' → g * v' = v' * g := fun g h => by
    calc g * v' = g * v' * g⁻¹ * g := by group
      _ = v' * g := by rw [h]
  refine ⟨v', v'.2, hv1, fun s hs => hcomm_of s (hfix ⟨s, hTM.le hs⟩ (Subgroup.mem_sup_right (hmemTb _ hs))), ?_⟩
  set J : Subgroup G := (R.comap π).map M.subtype with hJ
  have hJM : J ≤ M := Subgroup.map_subtype_le _
  have hmemJ : ∀ m : ↥M, (m : G) ∈ J ↔ π m ∈ R := by
    intro m
    constructor
    · rintro ⟨m', hm', hmm'⟩
      have : m' = m := Subtype.ext hmm'
      rw [← this]
      exact hm'
    · intro h
      exact ⟨m, h, rfl⟩
  have hJv : J ≤ centralizer ({(v' : G)} : Set G) := by
    rintro _ ⟨m, hm, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hcomm_of _ (hfix m (Subgroup.mem_sup_left hm))
  have hTJ : T ≤ normalizer (J : Set G) := by
    intro t ht
    apply Subgroup.mem_normalizer_fintype
    rintro _ ⟨m, hm, rfl⟩
    have htM := hTM.le ht
    refine ⟨⟨t, htM⟩ * m * ⟨t, htM⟩⁻¹, ?_, rfl⟩
    show π (⟨t, htM⟩ * m * ⟨t, htM⟩⁻¹) ∈ R
    rw [map_mul, map_mul, map_inv]
    exact (Subgroup.mem_normalizer_iff.1 (hRT (hmemTb _ ht)) _).1 hm
  set J₀ : Subgroup G := (S₀.comap π).map M.subtype with hJ₀
  have hJ₀J : J₀ ≤ J := Subgroup.map_mono (Subgroup.comap_mono inf_le_left)
  have hmemJ₀ : ∀ m : ↥M, (m : G) ∈ J₀ ↔ π m ∈ S₀ := by
    intro m
    constructor
    · rintro ⟨m', hm', hmm'⟩
      have : m' = m := Subtype.ext hmm'
      rw [← this]
      exact hm'
    · intro h
      exact ⟨m, h, rfl⟩
  set S : Subgroup G := T ⊓ J with hSdef
  have hSJ₀ : S ≤ J₀ := by
    rintro x ⟨hxT, hxJ⟩
    have hxM := hTM.le hxT
    exact (hmemJ₀ ⟨x, hxM⟩).2 ⟨(hmemJ ⟨x, hxM⟩).1 hxJ, hmemTb ⟨x, hxM⟩ hxT⟩
  have hSJ : CFSG.ABGLocalTools.IsSylowOf 2 S J := by
    have h1 : CFSG.ABGLocalTools.IsSylowOf 2 T (J ⊔ T) := hTM.of_le le_sup_right (sup_le hJM hTM.le)
    exact h1.inf_of_le_normalizer le_sup_left (sup_le Subgroup.le_normalizer hTJ)
  have hSJ₀' : CFSG.ABGLocalTools.IsSylowOf 2 S J₀ := hSJ.of_le hSJ₀ hJ₀J
  have hTS : T ≤ normalizer (S : Set G) := by
    intro t ht
    apply Subgroup.mem_normalizer_fintype
    rintro x ⟨hxT, hxJ⟩
    exact ⟨T.mul_mem (T.mul_mem ht hxT) (T.inv_mem ht),
      (Subgroup.mem_normalizer_iff.1 (hTJ ht) x).1 hxJ⟩
  set N : Subgroup G := J ⊓ normalizer (S : Set G) with hNdef
  have hSN : S ≤ N := le_inf hSJ.le Subgroup.le_normalizer
  have hNJ : N ≤ J := inf_le_left
  have hSN' : CFSG.ABGLocalTools.IsSylowOf 2 S N := hSJ.of_le hSN hNJ
  have hTN : T ≤ normalizer (N : Set G) := by
    intro t ht
    apply Subgroup.mem_normalizer_fintype
    rintro n ⟨hnJ, hnS⟩
    refine ⟨(Subgroup.mem_normalizer_iff.1 (hTJ ht) n).1 hnJ, ?_⟩
    apply Subgroup.mem_normalizer_fintype
    intro s hs
    have h1 : t⁻¹ * s * t ∈ S := by
      have := (Subgroup.mem_normalizer_iff.1 (hTS (T.inv_mem ht)) s).1 hs
      simpa using this
    have h2 : n * (t⁻¹ * s * t) * n⁻¹ ∈ S := (Subgroup.mem_normalizer_iff.1 hnS _).1 h1
    have h3 := (Subgroup.mem_normalizer_iff.1 (hTS ht) _).1 h2
    have e : t * n * t⁻¹ * s * (t * n * t⁻¹)⁻¹ = t * (n * (t⁻¹ * s * t) * n⁻¹) * t⁻¹ := by group
    rw [e]
    exact h3
  obtain ⟨m₀, hm₀⟩ := hπs z
  have hm₀J : (m₀ : G) ∈ J := (hmemJ m₀).2 (hm₀ ▸ hzR)
  have hm₀J₀ : ∀ x ∈ J₀, (m₀ : G) * x * (m₀ : G)⁻¹ ∈ J₀ := by
    rintro _ ⟨y, hy, rfl⟩
    refine (hmemJ₀ (m₀ * y * m₀⁻¹)).2 ?_
    rw [map_mul, map_mul, map_inv, hm₀]
    have h1 := Subgroup.mem_subgroupOf.1 (hRn.conj_mem ⟨π y, hy.1⟩ hy ⟨z, hzR⟩)
    simpa using h1
  set S' : Subgroup G := S.map (MulAut.conj (m₀ : G)).toMonoidHom with hS'
  have hS'J₀ : CFSG.ABGLocalTools.IsSylowOf 2 S' J₀ := by
    refine CFSG.ABGLocalTools.isSylowOf_of_card ?_ ?_
    · rintro _ ⟨x, hx, rfl⟩
      exact hm₀J₀ x (hSJ₀ hx)
    · rw [hS', Subgroup.card_map_of_injective (MulAut.conj _).injective]
      exact hSJ₀'.card_eq
  obtain ⟨j₀, hj₀, hj₀S⟩ := hSJ₀'.exists_mem_conj hS'J₀
  set n : G := j₀⁻¹ * (m₀ : G) with hn
  have hnJ : n ∈ J := J.mul_mem (J.inv_mem (hJ₀J hj₀)) hm₀J
  have hnN : n ∈ N := by
    refine ⟨hnJ, ?_⟩
    apply Subgroup.mem_normalizer_fintype
    intro s hs
    have h1 : (m₀ : G) * s * (m₀ : G)⁻¹ ∈ S' := ⟨s, hs, rfl⟩
    have h2 := (hj₀S _).1 h1
    have e : n * s * n⁻¹ = j₀⁻¹ * ((m₀ : G) * s * (m₀ : G)⁻¹) * j₀ := by
      rw [hn]
      group
    rw [e]
    exact h2
  have hnM : n ∈ M := hJM hnJ
  have hj₀M : j₀ ∈ M := hJM (hJ₀J hj₀)
  have hπj₀ : π ⟨j₀, hj₀M⟩ ∈ S₀ := (hmemJ₀ ⟨j₀, hj₀M⟩).1 hj₀
  have hπn : π ⟨n, hnM⟩ = (π ⟨j₀, hj₀M⟩)⁻¹ * z := by
    rw [← hm₀, ← map_inv, ← map_mul]
    congr 1
  have hπnR : π ⟨n, hnM⟩ ∈ R := (hmemJ ⟨n, hnM⟩).1 hnJ
  have hpn : p ∣ orderOf n := by
    have h1 : p ∣ orderOf (π ⟨n, hnM⟩) := by
      haveI : (S₀.subgroupOf R).Normal := hRn
      refine uc22p22r_dvd_orderOf_quot hS₀2 hp hp2 hzR hzo hπnR ?_
      have h2 := Subgroup.mem_subgroupOf.1 (hRn.conj_mem ⟨_, hπj₀.1⟩ hπj₀ ⟨z, hzR⟩⁻¹)
      have e : (π ⟨n, hnM⟩)⁻¹ * z = z⁻¹ * π ⟨j₀, hj₀M⟩ * z⁻¹⁻¹ := by
        rw [hπn]
        group
      rw [e]
      simpa using h2
    have h2 : orderOf (π ⟨n, hnM⟩) ∣ orderOf (⟨n, hnM⟩ : ↥M) := orderOf_map_dvd π _
    rw [Subgroup.orderOf_mk] at h2
    exact h1.trans h2
  have hpN : p ∣ Nat.card N := by
    have h1 : orderOf (⟨n, hnN⟩ : ↥N) ∣ Nat.card N := orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk] at h1
    exact hpn.trans h1
  haveI hSnN : (S.subgroupOf N).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hSN).2 inf_le_right
  have hS2 : IsPGroup 2 ↥(S.subgroupOf N) := hSN'.isPGroup.comap_subtype
  have hÑodd : ¬ 2 ∣ Nat.card (↥N ⧸ S.subgroupOf N) := by
    have h1 := (CFSG.ABGLocalTools.isSylowOf_iff.1 hSN').2.2
    rwa [Subgroup.relIndex, Subgroup.index_eq_card] at h1
  have hÑp : p ∣ Nat.card (↥N ⧸ S.subgroupOf N) := by
    have h1 := Subgroup.card_mul_index (S.subgroupOf N)
    rw [Subgroup.index_eq_card] at h1
    have hpS : ¬ p ∣ Nat.card ↥(S.subgroupOf N) := by
      obtain ⟨k, hk⟩ := hS2.exists_card_eq
      rw [hk]
      intro h
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h))
    have h2 : p ∣ Nat.card ↥(S.subgroupOf N) * Nat.card (↥N ⧸ S.subgroupOf N) := h1 ▸ hpN
    exact (hp.dvd_mul.1 h2).resolve_left hpS
  let ρ₀ : ↥T →* MulAut ↥N := N.normalizerMonoidHom.comp (Subgroup.inclusion hTN)
  have hρ₀ : ∀ (t : ↥T) (x : ↥N), ((ρ₀ t x : ↥N) : G) = (t : G) * x * (t : G)⁻¹ := by
    intro t x
    simp [ρ₀]
  have hρ₀S : ∀ t : ↥T, (S.subgroupOf N).map (ρ₀ t).toMonoidHom = S.subgroupOf N := by
    intro t
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      have hy' : (y : G) ∈ S := hy
      show ((ρ₀ t y : ↥N) : G) ∈ S
      rw [hρ₀]
      exact (Subgroup.mem_normalizer_iff.1 (hTS t.2) _).1 hy'
    · intro hx
      have hx' : (x : G) ∈ S := hx
      refine ⟨(ρ₀ t)⁻¹ x, ?_, by simp⟩
      show (((ρ₀ t)⁻¹ x : ↥N) : G) ∈ S
      have h1 : ((ρ₀ t⁻¹ x : ↥N) : G) = (t : G)⁻¹ * x * (t : G) := by
        rw [hρ₀]
        simp
      have h2 : (ρ₀ t)⁻¹ x = ρ₀ t⁻¹ x := by rw [map_inv]
      rw [h2, h1]
      have := (Subgroup.mem_normalizer_iff.1 (hTS (T.inv_mem t.2)) _).1 hx'
      simpa using this
  let θ : ↥T →* MulAut (↥N ⧸ S.subgroupOf N) := quotAutHom (S.subgroupOf N) ρ₀ hρ₀S
  have hθ : ∀ (t : ↥T) (x : ↥N), θ t (QuotientGroup.mk x) = QuotientGroup.mk (ρ₀ t x) :=
    fun t x => quotAutHom_mk _ _ _ t x
  have hT2 : IsPGroup 2 ↥T := hTM.isPGroup
  obtain ⟨Ps, hPs⟩ := CFSG.OrderReductions.InvariantSylow.exists_invariant_sylow_of_coprime 2 p hT2 hÑodd θ
  set Ñ := ↥N ⧸ S.subgroupOf N with hÑ
  set P0 : Subgroup Ñ := (Ps : Subgroup Ñ) with hP0
  let E : Subgroup Ñ :=
    { carrier := {x | x ∈ P0 ∧ (∀ y ∈ P0, x * y = y * x) ∧ x ^ p = 1}
      mul_mem' := by
        rintro a b ⟨ha, hac, hap⟩ ⟨hb, hbc, hbp⟩
        refine ⟨P0.mul_mem ha hb, fun y hy => ?_, ?_⟩
        · rw [mul_assoc, hbc y hy, ← mul_assoc, hac y hy, mul_assoc]
        · rw [(Commute.mul_pow (hac b hb) p), hap, hbp, one_mul]
      one_mem' := ⟨P0.one_mem, fun y _ => by rw [one_mul, mul_one], one_pow p⟩
      inv_mem' := by
        rintro a ⟨ha, hac, hap⟩
        refine ⟨P0.inv_mem ha, fun y hy => ?_, by rw [inv_pow, hap, inv_one]⟩
        have h := hac y hy
        calc a⁻¹ * y = a⁻¹ * (y * a) * a⁻¹ := by group
          _ = a⁻¹ * (a * y) * a⁻¹ := by rw [h]
          _ = y * a⁻¹ := by group }
  have hmemE : ∀ x : Ñ, x ∈ E ↔ x ∈ P0 ∧ (∀ y ∈ P0, x * y = y * x) ∧ x ^ p = 1 := fun x => Iff.rfl
  have hEinv : ∀ (t : ↥T) (x : Ñ), x ∈ E → θ t x ∈ E := by
    intro t x hx
    obtain ⟨hxP, hxc, hxp⟩ := (hmemE x).1 hx
    have hmap := hPs t
    refine (hmemE _).2 ⟨?_, fun y hy => ?_, by rw [← map_pow, hxp, map_one]⟩
    · rw [← hmap]
      exact ⟨x, hxP, rfl⟩
    · rw [← hmap] at hy
      obtain ⟨y', hy', rfl⟩ := hy
      show θ t x * θ t y' = θ t y' * θ t x
      rw [← map_mul, ← map_mul, hxc y' hy']
  have hP0p : IsPGroup p ↥P0 := Ps.isPGroup'
  have hP0nt : Nontrivial ↥P0 := by
    rw [← Finite.one_lt_card_iff_nontrivial]
    have h1 : Nat.card ↥P0 = p ^ (Nat.card Ñ).factorization p := Ps.card_eq_multiplicity
    have h2 : 1 ≤ (Nat.card Ñ).factorization p :=
      (hp.dvd_iff_one_le_factorization Nat.card_pos.ne').1 hÑp
    rw [h1]
    calc 1 < p := hp.one_lt
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ (Nat.card Ñ).factorization p := Nat.pow_le_pow_right hp.pos h2
  have hZnt : Nontrivial (Subgroup.center ↥P0) := hP0p.center_nontrivial
  have hZp : p ∣ Nat.card (Subgroup.center ↥P0) := by
    obtain ⟨k, hk⟩ := (hP0p.to_subgroup (Subgroup.center ↥P0)).exists_card_eq
    have hk0 : k ≠ 0 := by
      rintro rfl
      have := Finite.one_lt_card_iff_nontrivial.2 hZnt
      rw [hk, pow_zero] at this
      exact lt_irrefl 1 this
    rw [hk]
    exact dvd_pow_self p hk0
  obtain ⟨c, hco⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.center ↥P0)) p hZp
  have hcE : (((c : ↥P0) : Ñ)) ∈ E := by
    refine (hmemE _).2 ⟨(c : ↥P0).2, fun y hy => ?_, ?_⟩
    · have := Subgroup.mem_center_iff.1 c.2 ⟨y, hy⟩
      exact (congrArg Subtype.val this).symm
    · have h1 : c ^ p = 1 := hco ▸ pow_orderOf_eq_one c
      have h2 := congrArg (fun u : Subgroup.center ↥P0 => (((u : ↥P0) : Ñ))) h1
      simpa using h2
  have hc1 : (((c : ↥P0) : Ñ)) ≠ 1 := by
    intro h
    have : c = 1 := Subtype.ext (Subtype.ext h)
    rw [this, orderOf_one] at hco
    exact hp.one_lt.ne' hco.symm
  have hE1 : E ≠ ⊥ := fun h => hc1 (by
    have : (((c : ↥P0) : Ñ)) ∈ (⊥ : Subgroup Ñ) := h ▸ hcE
    simpa using this)
  set Sb : Subgroup ↥N := S.subgroupOf N with hSb
  set q₀ : ↥N →* Ñ := QuotientGroup.mk' Sb with hq₀
  set Bt : Subgroup ↥N := E.comap q₀ with hBt
  have hSbBt : Sb ≤ Bt := by
    intro x hx
    show q₀ x ∈ E
    rw [hq₀, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff x).2 hx]
    exact E.one_mem
  obtain ⟨Q⟩ := (inferInstance : Nonempty (Sylow p ↥Bt))
  set A₀ : Subgroup ↥N := (Q : Subgroup ↥Bt).map Bt.subtype with hA₀
  have hA₀Bt : A₀ ≤ Bt := Subgroup.map_subtype_le _
  have hA₀p : IsPGroup p ↥A₀ := Q.isPGroup'.map Bt.subtype
  have hA₀S : Sb ⊓ A₀ = ⊥ := uc22p22r_inf_eq_bot_of_coprime hp hp2 hS2 hA₀p
  have hinj : Function.Injective (q₀.comp A₀.subtype) := by
    rw [injective_iff_map_eq_one]
    intro a ha
    have h1 : (a : ↥N) ∈ Sb := (QuotientGroup.eq_one_iff _).1 ha
    have h2 : (a : ↥N) ∈ Sb ⊓ A₀ := ⟨h1, a.2⟩
    rw [hA₀S, Subgroup.mem_bot] at h2
    exact Subtype.ext h2
  have hBtcard : Nat.card ↥Bt = Nat.card ↥Sb * Nat.card ↥E := by
    let f : ↥Bt →* Ñ := q₀.comp Bt.subtype
    have hrange : f.range = E := by
      ext y
      constructor
      · rintro ⟨b, rfl⟩
        exact b.2
      · intro hy
        obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective Sb y
        exact ⟨⟨x, hy⟩, rfl⟩
    have hker : f.ker = Sb.subgroupOf Bt := by
      ext b
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
      exact QuotientGroup.eq_one_iff _
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv, hrange, hker,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSbBt).toEquiv, mul_comm]
  have hEp : IsPGroup p ↥E := fun x => ⟨1, Subtype.ext (by simpa using ((hmemE x).1 x.2).2.2)⟩
  obtain ⟨kE, hkE⟩ := hEp.exists_card_eq
  obtain ⟨kS, hkS⟩ := hS2.exists_card_eq
  have hA₀card : Nat.card ↥A₀ = Nat.card ↥E := by
    rw [hA₀, Subgroup.card_map_of_injective Bt.subtype_injective, Q.card_eq_multiplicity, hBtcard, hkS,
      hkE, Nat.factorization_mul (pow_ne_zero _ two_ne_zero) (pow_ne_zero _ hp.ne_zero), Finsupp.add_apply,
      Nat.factorization_pow_self hp]
    have h0 : (2 ^ kS).factorization p = 0 := by
      refine Nat.factorization_eq_zero_of_not_dvd fun h => hp2 ?_
      exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h)
    rw [h0, zero_add]
  have himg : A₀.map q₀ = E := by
    have hle : A₀.map q₀ ≤ E := by
      rintro _ ⟨a, ha, rfl⟩
      exact hA₀Bt ha
    refine le_antisymm hle ?_
    have hcard : Nat.card ↥(A₀.map q₀) = Nat.card ↥A₀ := by
      have : A₀.map q₀ = (q₀.comp A₀.subtype).range := by
        rw [MonoidHom.range_comp, Subgroup.range_subtype]
      rw [this]
      exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
    exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hcard, hA₀card])).ge
  set A : Subgroup G := A₀.map N.subtype with hAdef
  have hAN : A ≤ N := Subgroup.map_subtype_le _
  have hqA : ∀ a₀ ∈ A₀, q₀ a₀ ∈ E := fun a₀ ha₀ => hA₀Bt ha₀
  have hA₀inj : ∀ a ∈ A₀, ∀ b ∈ A₀, q₀ a = q₀ b → a = b := fun a ha b hb h =>
    congrArg Subtype.val (hinj (a₁ := ⟨a, ha⟩) (a₂ := ⟨b, hb⟩) h)
  have hAe : ∀ a ∈ A, a ^ p = 1 := by
    rintro _ ⟨a₀, ha₀, rfl⟩
    have h1 : q₀ (a₀ ^ p) = q₀ 1 := by rw [map_pow, ((hmemE _).1 (hqA a₀ ha₀)).2.2, map_one]
    have h2 := hA₀inj _ (A₀.pow_mem ha₀ p) _ A₀.one_mem h1
    have h3 := congrArg Subtype.val h2
    rw [Subgroup.coe_pow, Subgroup.coe_one] at h3
    exact h3
  have hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := by
    rintro _ ⟨a₀, ha₀, rfl⟩ _ ⟨b₀, hb₀, rfl⟩
    have h1 : q₀ (a₀ * b₀) = q₀ (b₀ * a₀) := by
      rw [map_mul, map_mul]
      exact ((hmemE _).1 (hqA a₀ ha₀)).2.1 _ ((hmemE _).1 (hqA b₀ hb₀)).1
    have h2 := hA₀inj _ (A₀.mul_mem ha₀ hb₀) _ (A₀.mul_mem hb₀ ha₀) h1
    simpa using congrArg Subtype.val h2
  have hA1 : A ≠ ⊥ := by
    intro h
    have h1 : A₀ = ⊥ := by
      rw [eq_bot_iff]
      intro a₀ ha₀
      have : (a₀ : G) ∈ A := ⟨a₀, ha₀, rfl⟩
      rw [h, Subgroup.mem_bot] at this
      exact Subgroup.mem_bot.2 (Subtype.ext this)
    have h2 : Nat.card ↥E = 1 := by rw [← hA₀card, h1, Subgroup.card_bot]
    exact hE1 (Subgroup.eq_bot_of_card_eq E h2)
  have hAp : IsPGroup p ↥A := hA₀p.map N.subtype
  set B : Subgroup G := Bt.map N.subtype with hBdef
  have hTB : T ≤ normalizer (B : Set G) := by
    intro t ht
    apply Subgroup.mem_normalizer_fintype
    rintro _ ⟨β, hβ, rfl⟩
    refine ⟨ρ₀ ⟨t, ht⟩ β, ?_, hρ₀ ⟨t, ht⟩ β⟩
    show q₀ (ρ₀ ⟨t, ht⟩ β) ∈ E
    rw [hq₀, QuotientGroup.mk'_apply, ← hθ]
    exact hEinv ⟨t, ht⟩ _ hβ
  have hAB : (A : Set G) * (S : Set G) = B := by
    ext b
    constructor
    · rintro ⟨_, ⟨a₀, ha₀, rfl⟩, s, hs, rfl⟩
      have hsN : s ∈ N := hSN hs
      refine ⟨a₀ * ⟨s, hsN⟩, Bt.mul_mem (hA₀Bt ha₀) (hSbBt hs), rfl⟩
    · rintro ⟨β, hβ, rfl⟩
      have hβE : q₀ β ∈ A₀.map q₀ := himg ▸ hβ
      obtain ⟨a₀, ha₀, hqa⟩ := hβE
      have h1 : a₀⁻¹ * β ∈ Sb := by
        rw [hq₀, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hqa
        exact hqa
      refine ⟨a₀, ⟨a₀, ha₀, rfl⟩, ((a₀⁻¹ * β : ↥N) : G), h1, ?_⟩
      simp
  have hSA : (S : Set G) * (A : Set G) = B := by
    ext b
    constructor
    · rintro ⟨s, hs, _, ⟨a₀, ha₀, rfl⟩, rfl⟩
      have hsN : s ∈ N := hSN hs
      refine ⟨⟨s, hsN⟩ * a₀, Bt.mul_mem (hSbBt hs) (hA₀Bt ha₀), rfl⟩
    · rintro ⟨β, hβ, rfl⟩
      have hβE : q₀ β ∈ A₀.map q₀ := himg ▸ hβ
      obtain ⟨a₀, ha₀, hqa⟩ := hβE
      have h1 : β * a₀⁻¹ ∈ Sb := by
        have h2 : q₀ (β * a₀⁻¹) = 1 := by rw [map_mul, map_inv, hqa, mul_inv_cancel]
        exact (QuotientGroup.eq_one_iff _).1 h2
      refine ⟨((β * a₀⁻¹ : ↥N) : G), h1, a₀, ⟨a₀, ha₀, rfl⟩, ?_⟩
      simp
  have hSTle : S ≤ T := inf_le_left
  have hperm : Permutes A T := by
    unfold Permutes
    calc (A : Set G) * (T : Set G) = (A : Set G) * ((S : Set G) * (T : Set G)) := by
          rw [uc22p22r_set_mul_of_le hSTle]
      _ = (B : Set G) * (T : Set G) := by rw [← mul_assoc, hAB]
      _ = (T : Set G) * (B : Set G) :=
          (Subgroup.set_mul_normalizer_comm (T : Set G) B hTB).symm
      _ = (T : Set G) * ((S : Set G) * (A : Set G)) := by rw [hSA]
      _ = (T : Set G) * (A : Set G) := by rw [← mul_assoc, uc22p22r_mul_set_of_le hSTle]
  have hJrk : CFSG.Open.pRank p J ≤ 2 := by
    apply CFSG.SectionRank.pRank_le hp.one_lt
    intro E' hE'J hE'
    have hE'M : E' ≤ M := hE'J.trans hJM
    let φ' : ↥E' →* MBar M V := π.comp (Subgroup.inclusion hE'M)
    have hE'p : IsPGroup p ↥E' := fun x => ⟨1, Subtype.ext (by simpa using hE'.2 x x.2)⟩
    have hrange : Nat.card φ'.range ≤ p := by
      haveI : (S₀.subgroupOf R).Normal := hRn
      refine uc22p22r_card_pSubgroup_le inf_le_left hS₀2 hp hp2 hzR (hzo ▸ pow_orderOf_eq_one z) hRz
        ?_ (hE'p.of_surjective φ'.rangeRestrict φ'.rangeRestrict_surjective)
      rintro _ ⟨x, rfl⟩
      exact (hmemJ ⟨x, hE'M x.2⟩).1 (hE'J x.2)
    have hker : Nat.card φ'.ker ≤ p := by
      set K' : Subgroup G := φ'.ker.map E'.subtype with hK'
      have hK'le : K' ≤ M ⊓ centralizer (V : Set G) := by
        rintro _ ⟨x, hx, rfl⟩
        refine ⟨hE'M x.2, ?_⟩
        have h1 : π ⟨x, hE'M x.2⟩ = 1 := hx
        exact (uc22br_gt_mk_eq_one_iff hVM ⟨x, hE'M x.2⟩).1 h1
      have hK'e : IsElemAbelian p K' := by
        refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩
        · obtain ⟨a', -, ha'⟩ := a.2
          obtain ⟨b', -, hb'⟩ := b.2
          show (a : G) * b = b * a
          rw [← ha', ← hb']
          exact congrArg Subtype.val (hE'.1.1.comm a' b')
        · obtain ⟨x', -, rfl⟩ := hx
          exact hE'.2 _ x'.2
      have hK'p : IsPGroup p ↥K' := fun x => ⟨1, Subtype.ext (by simpa using hK'e.2 x x.2)⟩
      obtain ⟨j, hj⟩ := hK'p.exists_card_eq
      have hj1 : j ≤ 1 := (CFSG.SectionRank.le_pRank hp.one_lt hK'le hK'e hj).trans hrk
      have hK'card : Nat.card ↥K' = Nat.card φ'.ker :=
        (Nat.card_congr (Subgroup.equivMapOfInjective φ'.ker E'.subtype E'.subtype_injective).toEquiv).symm
      rw [← hK'card, hj]
      calc p ^ j ≤ p ^ 1 := Nat.pow_le_pow_right hp.pos hj1
        _ = p := pow_one p
    have hcard : Nat.card ↥E' = Nat.card φ'.ker * Nat.card φ'.range := by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup φ'.ker,
        Nat.card_congr (QuotientGroup.quotientKerEquivRange φ').toEquiv, mul_comm]
    rw [hcard, pow_two]
    exact Nat.mul_le_mul hker hrange
  refine ⟨A, hAN.trans (hNJ.trans hJM), hAN.trans (hNJ.trans hJv), hA1, hAp, hAe, hAc, hperm, ?_⟩
  exact (CFSG.SectionRank.pRank_mono hp.one_lt (hAN.trans hNJ)).trans hJrk

end Lift

end CFSG.LocalAnalysis.UniquenessCase.UC22
