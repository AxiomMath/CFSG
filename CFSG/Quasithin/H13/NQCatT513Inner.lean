module

public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
public import CFSG.Quasithin.H13.NQCatA314Gen
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PerfectCentralAutomorphism
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Background.A3Structure312Quotient

public section

namespace CFSG.Quasithin.H13.NQCat.T513P

open CFSG.Open CFSG.QuasithinUnique CFSG.ComponentClassification.OuterAutomorphisms
open scoped Pointwise

variable {A : Type} [Group A]

@[expose] def conjQ (Q : Subgroup A) (n : A) (hn : n ∈ Subgroup.normalizer (Q : Set A)) :
    ↥Q ≃* ↥Q where
  toFun q := ⟨n * q * n⁻¹, (Subgroup.mem_normalizer_iff.mp hn q).mp q.2⟩
  invFun q := ⟨n⁻¹ * q * n, by
    have h := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hn) q).mp q.2
    simpa using h⟩
  left_inv q := by
    apply Subtype.ext
    simp [mul_assoc]
  right_inv q := by
    apply Subtype.ext
    simp [mul_assoc]
  map_mul' q r := by
    apply Subtype.ext
    simp [mul_assoc]

@[expose] noncomputable def actQ (Q : Subgroup A) :
    ↥(Subgroup.normalizer (Q : Set A)) →* MulAut ↥Q where
  toFun n := conjQ Q n n.2
  map_one' := by
    ext q
    simp [conjQ]
  map_mul' m n := by
    ext q
    simp [conjQ, mul_assoc]

theorem actQ_apply (Q : Subgroup A) (n : ↥(Subgroup.normalizer (Q : Set A))) (q : ↥Q) :
    ((actQ Q n q : ↥Q) : A) = n * q * n⁻¹ := rfl

theorem actQ_eq_one_iff (Q : Subgroup A) (n : ↥(Subgroup.normalizer (Q : Set A))) :
    actQ Q n = 1 ↔ (n : A) ∈ Subgroup.centralizer (Q : Set A) := by
  rw [Subgroup.mem_centralizer_iff]
  constructor
  · intro h q hq
    have h1 := congrArg (fun φ : MulAut ↥Q => ((φ ⟨q, hq⟩ : ↥Q) : A)) h
    simp only [actQ_apply] at h1
    change (n : A) * q * (n : A)⁻¹ = q at h1
    calc q * (n : A) = (n : A) * q * (n : A)⁻¹ * (n : A) := by rw [h1]
      _ = (n : A) * q := by group
  · intro h
    ext q
    show (n : A) * q * (n : A)⁻¹ = q
    rw [← h q q.2]
    group

theorem actQ_of_mem (Q : Subgroup A) (q : ↥Q) :
    actQ Q ⟨q, Subgroup.le_normalizer q.2⟩ = MulAut.conj q := by
  ext r
  rfl

theorem coe_sup_eq_mul {G : Type*} [Group G] (H K : Subgroup G)
    (h : (H : Set G) * (K : Set G) = (K : Set G) * (H : Set G)) :
    ((H ⊔ K : Subgroup G) : Set G) = (H : Set G) * (K : Set G) := by
  let T : Subgroup G :=
    { carrier := (H : Set G) * K
      one_mem' := ⟨1, H.one_mem, 1, K.one_mem, one_mul 1⟩
      mul_mem' := by
        rintro _ _ ⟨a, ha, b, hb, rfl⟩ ⟨c, hc, d, hd, rfl⟩
        have hbc : b * c ∈ (K : Set G) * H := ⟨b, hb, c, hc, rfl⟩
        rw [← h] at hbc
        obtain ⟨c', hc', b', hb', hcb⟩ := hbc
        have hcb : c' * b' = b * c := hcb
        refine ⟨a * c', H.mul_mem ha hc', b' * d, K.mul_mem hb' hd, ?_⟩
        calc a * c' * (b' * d) = a * (c' * b') * d := by group
          _ = a * (b * c) * d := by rw [hcb]
          _ = a * b * (c * d) := by group
      inv_mem' := by
        rintro _ ⟨a, ha, b, hb, rfl⟩
        have hba : b⁻¹ * a⁻¹ ∈ (K : Set G) * H := ⟨b⁻¹, K.inv_mem hb, a⁻¹, H.inv_mem ha, rfl⟩
        rw [← h] at hba
        rw [mul_inv_rev]
        exact hba }
  have hT : H ⊔ K = T := le_antisymm
    (sup_le (fun x hx => ⟨x, hx, 1, K.one_mem, mul_one x⟩)
      (fun x hx => ⟨1, H.one_mem, x, hx, one_mul x⟩))
    (fun x ⟨a, ha, b, hb, hab⟩ => hab ▸ Subgroup.mul_mem_sup ha hb)
  rw [hT]
  rfl

@[expose] def OddAutThreeInner (X : Type) [Group X] : Prop :=
  ∀ φ : MulAut X, Odd (orderOf φ) → ∃ k : ℕ, φ ^ (3 ^ k) ∈ inner X

@[expose] def CycOddPerm (X : Type) [Group X] (c : ℕ → Prop) : Prop :=
  ∀ T Dc : Subgroup X, IsSylowTwoOf T ⊤ → IsCyclic ↥Dc → Odd (Nat.card ↥Dc) →
    (Dc : Set X) * (T : Set X) = (T : Set X) * (Dc : Set X) →
      (∃ k : ℕ, Nat.card ↥Dc = 3 ^ k) ∨ c (Nat.card ↥Dc)

theorem oddAutThreeInner_of_card_outer_dvd {X : Type} [Group X] [Finite (Outer X)] {a b : ℕ}
    (h : Nat.card (Outer X) ∣ 2 ^ a * 3 ^ b) : OddAutThreeInner X := by
  intro φ hφ
  refine ⟨b, ?_⟩
  have h1 : orderOf (QuotientGroup.mk φ : Outer X) ∣ orderOf φ :=
    orderOf_map_dvd (QuotientGroup.mk' _) φ
  have h2 : orderOf (QuotientGroup.mk φ : Outer X) ∣ 2 ^ a * 3 ^ b :=
    (orderOf_dvd_natCard _).trans h
  have hodd : Odd (orderOf (QuotientGroup.mk φ : Outer X)) := Odd.of_dvd_nat hφ h1
  have hcop : Nat.Coprime (orderOf (QuotientGroup.mk φ : Outer X)) (2 ^ a) :=
    Nat.Coprime.pow_right _ (Nat.coprime_two_right.mpr hodd)
  have h3 : orderOf (QuotientGroup.mk φ : Outer X) ∣ 3 ^ b := hcop.dvd_of_dvd_mul_left h2
  have h4 : (QuotientGroup.mk φ : Outer X) ^ (3 ^ b) = 1 := orderOf_dvd_iff_pow_eq_one.mp h3
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at h4
  exact h4

theorem oddAutThreeInner_of_inner {X : Type} [Group X]
    (h : ∀ φ : MulAut X, Odd (orderOf φ) → φ ∈ inner X) : OddAutThreeInner X :=
  fun φ hφ => ⟨0, by rw [pow_zero, pow_one]; exact h φ hφ⟩

theorem OddAutThreeInner.of_equiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    (h : OddAutThreeInner X) : OddAutThreeInner Y := by
  intro φ hφ
  let ψ : MulAut X := MulAut.congr e.symm φ
  have hψ : Odd (orderOf ψ) := by
    rw [MulEquiv.orderOf_eq]
    exact hφ
  obtain ⟨k, hk⟩ := h ψ hψ
  refine ⟨k, ?_⟩
  have h1 : MulAut.congr e (ψ ^ (3 ^ k)) ∈ inner Y := by
    rw [← inner_map_congr e]
    exact ⟨_, hk, rfl⟩
  have h2 : MulAut.congr e (ψ ^ (3 ^ k)) = φ ^ (3 ^ k) := by
    rw [map_pow]
    congr 1
    ext x
    simp [ψ]
  rwa [h2] at h1

@[expose] noncomputable def descZ (X : Type) [Group X] :
    MulAut X →* MulAut (X ⧸ Subgroup.center X) where
  toFun σ := QuotientGroup.congr _ _ σ (Subgroup.map_center_eq σ)
  map_one' := by
    ext x
    induction x using QuotientGroup.induction_on with
    | H x => rfl
  map_mul' σ τ := by
    ext x
    induction x using QuotientGroup.induction_on with
    | H x => rfl

theorem descZ_mk {X : Type} [Group X] (σ : MulAut X) (x : X) :
    descZ X σ (x : X ⧸ Subgroup.center X) = ((σ x : X) : X ⧸ Subgroup.center X) := rfl

theorem mem_inner_of_descZ_mem_inner {X : Type} [Group X] (hX : Group.IsPerfect X)
    {σ : MulAut X} (h : descZ X σ ∈ inner (X ⧸ Subgroup.center X)) : σ ∈ inner X := by
  obtain ⟨x, hx⟩ := h
  induction x using QuotientGroup.induction_on with
  | H g =>
    refine ⟨g, (CFSG.GorensteinWalter.perfect_central_automorphism_eq hX σ (MulAut.conj g)
      fun s => ?_).symm⟩
    have h1 := congrArg (fun φ : MulAut (X ⧸ Subgroup.center X) =>
      φ (s : X ⧸ Subgroup.center X)) hx
    simp only [MulAut.conj_apply, descZ_mk] at h1
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
      QuotientGroup.eq] at h1
    have h2 : (σ s * (MulAut.conj g s)⁻¹) =
        (g * s * g⁻¹) * ((g * s * g⁻¹)⁻¹ * σ s) * (g * s * g⁻¹)⁻¹ := by
      rw [MulAut.conj_apply]
      group
    rw [h2]
    exact (inferInstance : (Subgroup.center X).Normal).conj_mem _ h1 _

theorem oddAutThreeInner_of_center {X : Type} [Group X] (hX : Group.IsPerfect X)
    (h : OddAutThreeInner (X ⧸ Subgroup.center X)) : OddAutThreeInner X := by
  intro φ hφ
  have hd : Odd (orderOf (descZ X φ)) := Odd.of_dvd_nat hφ (orderOf_map_dvd _ φ)
  obtain ⟨k, hk⟩ := h _ hd
  refine ⟨k, mem_inner_of_descZ_mem_inner hX ?_⟩
  rw [map_pow]
  exact hk

theorem ker_conj_eq_center (X : Type) [Group X] :
    (MulAut.conj : X →* MulAut X).ker = Subgroup.center X := by
  ext g
  rw [MonoidHom.mem_ker, Subgroup.mem_center_iff]
  constructor
  · intro h x
    have h1 := congrArg (fun φ : MulAut X => φ x) h
    simp only [MulAut.conj_apply, MulAut.one_apply] at h1
    calc x * g = g * x * g⁻¹ * g := by rw [h1]
      _ = g * x := by group
  · intro h
    ext x
    simp only [MulAut.conj_apply, MulAut.one_apply]
    rw [← h x]
    group

@[expose] noncomputable def innerEquivQuot (X : Type) [Group X] :
    ↥(inner X) ≃* X ⧸ Subgroup.center X :=
  ((QuotientGroup.quotientMulEquivOfEq (ker_conj_eq_center X).symm).trans
    (QuotientGroup.quotientKerEquivRange (MulAut.conj : X →* MulAut X))).symm

@[expose] noncomputable def quotCenterEquivOfBot {X : Type} [Group X]
    (h : Subgroup.center X = ⊥) : X ⧸ Subgroup.center X ≃* X :=
  (QuotientGroup.quotientMulEquivOfEq h).trans QuotientGroup.quotientBot

theorem CycOddPerm.of_equiv {X Y : Type} [Group X] [Group Y] [Finite X] {c : ℕ → Prop}
    (e : X ≃* Y) (h : CycOddPerm X c) : CycOddPerm Y c := by
  intro T Dc hT hcyc hodd hperm
  have : Finite Y := Finite.of_equiv _ e.toEquiv
  have hcard : Nat.card ↥(Dc.map e.symm.toMonoidHom) = Nat.card ↥Dc :=
    Subgroup.card_map_of_injective e.symm.injective
  have hT' : IsSylowTwoOf (T.map e.symm.toMonoidHom) ⊤ :=
    A312.isSylowTwoOf_top_map e.symm.toMonoidHom e.symm.surjective hT
  have hcyc' : IsCyclic ↥(Dc.map e.symm.toMonoidHom) :=
    isCyclic_of_surjective (Dc.equivMapOfInjective e.symm.toMonoidHom e.symm.injective).toMonoidHom
      (MulEquiv.surjective _)
  have hperm' : ((Dc.map e.symm.toMonoidHom : Subgroup X) : Set X) *
      ((T.map e.symm.toMonoidHom : Subgroup X) : Set X) =
      ((T.map e.symm.toMonoidHom : Subgroup X) : Set X) *
        ((Dc.map e.symm.toMonoidHom : Subgroup X) : Set X) := by
    simp only [Subgroup.coe_map]
    rw [← Set.image_mul, hperm, Set.image_mul]
  have h1 := h _ _ hT' hcyc' (hcard ▸ hodd) hperm'
  rwa [hcard] at h1

theorem cycOddPerm_inner {X M : Type} [Group X] [Group M] [Finite M] {c : ℕ → Prop}
    (e : X ⧸ Subgroup.center X ≃* M) (h : CycOddPerm M c) : CycOddPerm ↥(inner X) c :=
  h.of_equiv (e.symm.trans (innerEquivQuot X).symm)

theorem mem_of_mul_mem_of_coprime {Γ : Type} [Group Γ] {I : Subgroup Γ} [I.Normal] {s d : Γ}
    {a : ℕ} (hs : s ^ (2 ^ a) = 1) {m : ℕ} (hm : Odd m) (hd : d ^ m = 1) (h : s * d ∈ I) :
    s ∈ I ∧ d ∈ I := by
  have h1 : (QuotientGroup.mk s : Γ ⧸ I) = (QuotientGroup.mk d)⁻¹ := by
    rw [eq_inv_iff_mul_eq_one, ← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff]
    exact h
  have h2 : (QuotientGroup.mk s : Γ ⧸ I) ^ (2 ^ a) = 1 := by
    rw [← QuotientGroup.mk_pow, hs, QuotientGroup.mk_one]
  have h3 : (QuotientGroup.mk s : Γ ⧸ I) ^ m = 1 := by
    rw [h1, inv_pow, ← QuotientGroup.mk_pow, hd, QuotientGroup.mk_one, inv_one]
  have hcop : Nat.Coprime (2 ^ a) m := Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hm)
  have h4 : orderOf (QuotientGroup.mk s : Γ ⧸ I) ∣ 1 := by
    rw [← Nat.Coprime.gcd_eq_one hcop]
    exact Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h2) (orderOf_dvd_of_pow_eq_one h3)
  have hs1 : (QuotientGroup.mk s : Γ ⧸ I) = 1 := orderOf_eq_one_iff.mp (Nat.dvd_one.mp h4)
  have hsI : s ∈ I := (QuotientGroup.eq_one_iff s).mp hs1
  refine ⟨hsI, ?_⟩
  have : d = s⁻¹ * (s * d) := by group
  rw [this]
  exact I.mul_mem (I.inv_mem hsI) h

theorem subgroupOf_mul_comm {G : Type*} [Group G] {I H K : Subgroup G} (hH : H ≤ I) (hK : K ≤ I)
    (h : (H : Set G) * (K : Set G) = (K : Set G) * (H : Set G)) :
    ((H.subgroupOf I : Set ↥I) * (K.subgroupOf I : Set ↥I)) =
      (K.subgroupOf I : Set ↥I) * (H.subgroupOf I : Set ↥I) := by
  ext x
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    have h1 : (a : G) * b ∈ (K : Set G) * (H : Set G) :=
      h ▸ ⟨a, Subgroup.mem_subgroupOf.mp ha, b, Subgroup.mem_subgroupOf.mp hb, rfl⟩
    obtain ⟨k, hk, h', hh', he⟩ := h1
    exact ⟨⟨k, hK hk⟩, Subgroup.mem_subgroupOf.mpr hk, ⟨h', hH hh'⟩,
      Subgroup.mem_subgroupOf.mpr hh', Subtype.ext he⟩
  · rintro ⟨a, ha, b, hb, rfl⟩
    have h1 : (a : G) * b ∈ (H : Set G) * (K : Set G) :=
      h.symm ▸ ⟨a, Subgroup.mem_subgroupOf.mp ha, b, Subgroup.mem_subgroupOf.mp hb, rfl⟩
    obtain ⟨h', hh', k, hk, he⟩ := h1
    exact ⟨⟨h', hH hh'⟩, Subgroup.mem_subgroupOf.mpr hh', ⟨k, hK hk⟩,
      Subgroup.mem_subgroupOf.mpr hk, Subtype.ext he⟩

theorem three_or_of_inner [Finite A] {Q S D : Subgroup A}
    (hSN : S ≤ Subgroup.normalizer (Q : Set A)) (hDN : D ≤ Subgroup.normalizer (Q : Set A))
    (hS2 : IsPGroup 2 ↥S) (hsyl : IsSylowTwoOf (S ⊓ Q) Q) (hDc : IsCyclic ↥D)
    (hDo : Odd (Nat.card ↥D)) (hperm : (D : Set A) * (S : Set A) = (S : Set A) * (D : Set A))
    (hout : OddAutThreeInner ↥Q) {c : ℕ → Prop} (hDT : CycOddPerm ↥(inner ↥Q) c) :
    (∀ d ∈ D, ∃ k : ℕ, d ^ (3 ^ k) ∈ Subgroup.centralizer (Q : Set A)) ∨
      ∃ n, c n ∧ ∀ (d : A) (hd : d ∈ D) (k : ℕ), actQ Q ⟨d, hDN hd⟩ ^ (3 ^ k) ∈ inner ↥Q →
        d ^ (3 ^ k * n) ∈ Subgroup.centralizer (Q : Set A) := by
  classical
  set N := Subgroup.normalizer (Q : Set A) with hN
  set I : Subgroup (MulAut ↥Q) := inner ↥Q with hI
  set Dst : Subgroup (MulAut ↥Q) := (D.subgroupOf N).map (actQ Q) with hDst
  set Sst : Subgroup (MulAut ↥Q) := (S.subgroupOf N).map (actQ Q) with hSst
  have hpowD : ∀ d ∈ D, d ^ Nat.card ↥D = 1 := fun d hd => by
    have h1 : (⟨d, hd⟩ : ↥D) ^ Nat.card ↥D = 1 := pow_card_eq_one'
    exact congrArg Subtype.val h1
  have hDst_pow : ∀ x ∈ Dst, x ^ Nat.card ↥D = 1 := by
    rintro _ ⟨⟨d, hdN⟩, hd, rfl⟩
    rw [← map_pow]
    have h1 : (⟨d, hdN⟩ : ↥N) ^ Nat.card ↥D = 1 :=
      Subtype.ext (hpowD d (Subgroup.mem_subgroupOf.mp hd))
    rw [h1, map_one]
  have hSst_two : ∀ x ∈ Sst, ∃ a : ℕ, x ^ (2 ^ a) = 1 := by
    rintro _ ⟨⟨s, hsN⟩, hs, rfl⟩
    obtain ⟨a, ha⟩ := hS2 ⟨s, Subgroup.mem_subgroupOf.mp hs⟩
    refine ⟨a, ?_⟩
    rw [← map_pow]
    have h1 : (⟨s, hsN⟩ : ↥N) ^ (2 ^ a) = 1 := Subtype.ext (by
      have h2 := congrArg Subtype.val ha
      simpa using h2)
    rw [h1, map_one]
  have hpermst : (Dst : Set (MulAut ↥Q)) * (Sst : Set (MulAut ↥Q)) =
      (Sst : Set (MulAut ↥Q)) * (Dst : Set (MulAut ↥Q)) := by
    ext x
    constructor
    · rintro ⟨_, ⟨⟨d, hdN⟩, hd, rfl⟩, _, ⟨⟨s, hsN⟩, hs, rfl⟩, rfl⟩
      have h1 : d * s ∈ (S : Set A) * (D : Set A) :=
        hperm ▸ ⟨d, Subgroup.mem_subgroupOf.mp hd, s, Subgroup.mem_subgroupOf.mp hs, rfl⟩
      obtain ⟨s', hs', d', hd', h2⟩ := h1
      refine ⟨actQ Q ⟨s', hSN hs'⟩, ⟨⟨s', hSN hs'⟩, Subgroup.mem_subgroupOf.mpr hs', rfl⟩,
        actQ Q ⟨d', hDN hd'⟩, ⟨⟨d', hDN hd'⟩, Subgroup.mem_subgroupOf.mpr hd', rfl⟩, ?_⟩
      beta_reduce
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext h2
    · rintro ⟨_, ⟨⟨s, hsN⟩, hs, rfl⟩, _, ⟨⟨d, hdN⟩, hd, rfl⟩, rfl⟩
      have h1 : s * d ∈ (D : Set A) * (S : Set A) :=
        hperm.symm ▸ ⟨s, Subgroup.mem_subgroupOf.mp hs, d, Subgroup.mem_subgroupOf.mp hd, rfl⟩
      obtain ⟨d', hd', s', hs', h2⟩ := h1
      refine ⟨actQ Q ⟨d', hDN hd'⟩, ⟨⟨d', hDN hd'⟩, Subgroup.mem_subgroupOf.mpr hd', rfl⟩,
        actQ Q ⟨s', hSN hs'⟩, ⟨⟨s', hSN hs'⟩, Subgroup.mem_subgroupOf.mpr hs', rfl⟩, ?_⟩
      beta_reduce
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext h2
  set D₀ : Subgroup (MulAut ↥Q) := Dst ⊓ I with hD₀
  set T₀ : Subgroup (MulAut ↥Q) := Sst ⊓ I with hT₀
  have hDTperm : (D₀ : Set (MulAut ↥Q)) * (T₀ : Set (MulAut ↥Q)) =
      (T₀ : Set (MulAut ↥Q)) * (D₀ : Set (MulAut ↥Q)) := by
    ext x
    constructor
    · rintro ⟨d, ⟨hdD, hdI⟩, t, ⟨htS, htI⟩, rfl⟩
      have hx : d * t ∈ (Sst : Set (MulAut ↥Q)) * (Dst : Set (MulAut ↥Q)) :=
        hpermst ▸ ⟨d, hdD, t, htS, rfl⟩
      obtain ⟨s, hs, d', hd', he⟩ := hx
      have hsd : s * d' ∈ I := by
        have h2 : d * t ∈ I := I.mul_mem hdI htI
        rw [← he] at h2
        exact h2
      obtain ⟨a, ha⟩ := hSst_two s hs
      obtain ⟨hsI, hdI'⟩ := mem_of_mul_mem_of_coprime ha hDo (hDst_pow d' hd') hsd
      exact ⟨s, ⟨hs, hsI⟩, d', ⟨hd', hdI'⟩, he⟩
    · rintro ⟨t, ⟨htS, htI⟩, d, ⟨hdD, hdI⟩, rfl⟩
      have hx : t * d ∈ (Dst : Set (MulAut ↥Q)) * (Sst : Set (MulAut ↥Q)) :=
        hpermst.symm ▸ ⟨t, htS, d, hdD, rfl⟩
      obtain ⟨d', hd', s, hs, he⟩ := hx
      have hds : d' * s ∈ I := by
        have h2 : t * d ∈ I := I.mul_mem htI hdI
        rw [← he] at h2
        exact h2
      have hsd : s * d' ∈ I := by
        have h3 : s * d' = s * (d' * s) * s⁻¹ := by group
        rw [h3]
        exact (inner_normal ↥Q).conj_mem _ hds s
      obtain ⟨a, ha⟩ := hSst_two s hs
      obtain ⟨hsI, hdI'⟩ := mem_of_mul_mem_of_coprime ha hDo (hDst_pow d' hd') hsd
      exact ⟨d', ⟨hd', hdI'⟩, s, ⟨hs, hsI⟩, he⟩
  let ρ : ↥Q →* ↥I := (MulAut.conj : ↥Q →* MulAut ↥Q).codRestrict I fun q => ⟨q, rfl⟩
  have hρ : Function.Surjective ρ := by
    rintro ⟨_, ⟨q, rfl⟩⟩
    exact ⟨q, rfl⟩
  have hT₁ : IsSylowTwoOf (((S ⊓ Q).subgroupOf Q).map ρ) ⊤ :=
    A312.isSylowTwoOf_top_map ρ hρ (A314D.isSylowTwoOf_top_subgroupOf hsyl)
  have hT₁le : ((S ⊓ Q).subgroupOf Q).map ρ ≤ T₀.subgroupOf I := by
    rintro _ ⟨q, hq, rfl⟩
    rw [Subgroup.mem_subgroupOf]
    have hq' : (q : A) ∈ S ⊓ Q := Subgroup.mem_subgroupOf.mp hq
    refine ⟨?_, ⟨q, rfl⟩⟩
    show MulAut.conj q ∈ Sst
    rw [← actQ_of_mem Q q]
    exact ⟨⟨q, Subgroup.le_normalizer q.2⟩, Subgroup.mem_subgroupOf.mpr hq'.1, rfl⟩
  have hT₀syl : IsSylowTwoOf (T₀.subgroupOf I) ⊤ := by
    refine ⟨le_top, fun x => ?_, ?_⟩
    · obtain ⟨a, ha⟩ := hSst_two (x : MulAut ↥Q) (Subgroup.mem_subgroupOf.mp x.2).1
      refine ⟨a, Subtype.ext (Subtype.ext ?_)⟩
      exact ha
    · rw [show ((T₀.subgroupOf I).subgroupOf ⊤).index = (T₀.subgroupOf I).index from
        Subgroup.relIndex_top_right _]
      have h1 := hT₁.2.2
      rw [show ((((S ⊓ Q).subgroupOf Q).map ρ).subgroupOf ⊤).index =
        (((S ⊓ Q).subgroupOf Q).map ρ).index from Subgroup.relIndex_top_right _] at h1
      exact fun h2 => h1 (h2.trans (Subgroup.index_dvd_of_le hT₁le))
  have hDcyc : IsCyclic ↥Dst := by
    have : IsCyclic ↥(D.subgroupOf N) :=
      isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hDN).symm.toMonoidHom
        (Subgroup.subgroupOfEquivOfLe hDN).symm.surjective
    exact isCyclic_of_surjective ((actQ Q).subgroupMap (D.subgroupOf N))
      ((actQ Q).subgroupMap_surjective _)
  have hD₀cyc : IsCyclic ↥(D₀.subgroupOf I) := by
    have h1 : IsCyclic ↥(D₀.subgroupOf Dst) := Subgroup.isCyclic _
    let e1 : ↥(D₀.subgroupOf I) ≃* ↥D₀ := Subgroup.subgroupOfEquivOfLe inf_le_right
    let e2 : ↥(D₀.subgroupOf Dst) ≃* ↥D₀ := Subgroup.subgroupOfEquivOfLe inf_le_left
    exact isCyclic_of_surjective (e2.trans e1.symm).toMonoidHom (e2.trans e1.symm).surjective
  have hcardD₀ : Nat.card ↥(D₀.subgroupOf I) = Nat.card ↥D₀ :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
  have hD₀dvd : Nat.card ↥D₀ ∣ Nat.card ↥D := by
    refine (Subgroup.card_dvd_of_le inf_le_left).trans
      ((Subgroup.card_map_dvd (D.subgroupOf N) (actQ Q)).trans ?_)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDN).toEquiv]
  have hD₀odd : Odd (Nat.card ↥(D₀.subgroupOf I)) := by
    rw [hcardD₀]
    exact Odd.of_dvd_nat hDo hD₀dvd
  have hcase := hDT (T₀.subgroupOf I) (D₀.subgroupOf I) hT₀syl hD₀cyc hD₀odd
    (subgroupOf_mul_comm inf_le_right inf_le_right hDTperm)
  rw [hcardD₀] at hcase
  have hkey : ∀ (d : A) (hd : d ∈ D) (k : ℕ), actQ Q ⟨d, hDN hd⟩ ^ (3 ^ k) ∈ I →
      d ^ (3 ^ k * Nat.card ↥D₀) ∈ Subgroup.centralizer (Q : Set A) := by
    intro d hd k hk
    have hφ : actQ Q ⟨d, hDN hd⟩ ^ (3 ^ k) ∈ D₀ :=
      ⟨Dst.pow_mem ⟨⟨d, hDN hd⟩, Subgroup.mem_subgroupOf.mpr hd, rfl⟩ _, hk⟩
    have h1 : (⟨_, hφ⟩ : ↥D₀) ^ Nat.card ↥D₀ = 1 := pow_card_eq_one'
    have h2 : actQ Q (⟨d, hDN hd⟩ ^ (3 ^ k * Nat.card ↥D₀)) = 1 := by
      rw [map_pow, pow_mul]
      exact congrArg Subtype.val h1
    rw [actQ_eq_one_iff] at h2
    exact h2
  have hodd : ∀ (d : A) (hd : d ∈ D), Odd (orderOf (actQ Q ⟨d, hDN hd⟩)) := by
    intro d hd
    refine Odd.of_dvd_nat hDo (orderOf_dvd_of_pow_eq_one ?_)
    exact hDst_pow _ ⟨⟨d, hDN hd⟩, Subgroup.mem_subgroupOf.mpr hd, rfl⟩
  rcases hcase with ⟨m, hm⟩ | hc
  · left
    intro d hd
    obtain ⟨k, hk⟩ := hout _ (hodd d hd)
    refine ⟨k + m, ?_⟩
    have := hkey d hd k hk
    rwa [hm, ← pow_add] at this
  · exact Or.inr ⟨Nat.card ↥D₀, hc, hkey⟩

end CFSG.Quasithin.H13.NQCat.T513P
