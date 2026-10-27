module

public import CFSG.Assembly.GL83LieDefs
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
public import CFSG.Quasithin.Background.A4Defs
public import CFSG.Quasithin.Vol2.Ch3Sec3KGSylow

public section

namespace CFSG.Quasithin.H13.KGAutSyl

open CFSG.QuasithinUnique CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.Assembly.LowTwoRank

theorem autOddNormCent_of {Q : Type} [Group Q] [Finite Q]
    (hinj : Function.Injective (MulAut.conj : Q →* MulAut Q))
    (hAut : ∀ P : Subgroup Q, IsSylowTwoOf P ⊤ → IsPGroup 2 (MulAut ↥P))
    (hout : ¬ 4 ∣ Nat.card (Outer Q)) : AutOddNormCent Q := by
  intro A S hA hS d hd hodd s hs
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (MulAut Q) :=
    Finite.of_injective (fun e : MulAut Q => (e : Q → Q)) fun _ _ h => MulEquiv.ext (congrFun h)
  obtain ⟨hdN, -⟩ := Subgroup.mem_inf.mp hd
  have hdm : d ^ orderOf d = 1 := pow_orderOf_eq_one d
  have hSI : IsSylowTwoOf (S ⊓ inner Q) (inner Q) :=
    A4.isSylowTwoOf_inf_normal hS hA (fun g _ => Subgroup.mem_normalizer_iff.mpr fun h =>
      ⟨fun hh => (inner_normal Q).conj_mem h hh g, fun hh => by
        have := (inner_normal Q).conj_mem _ hh g⁻¹
        simpa [mul_assoc] using this⟩)
  have hNI : ∀ g ∈ Subgroup.normalizer (S : Set (MulAut Q)),
      g ∈ Subgroup.normalizer ((S ⊓ inner Q : Subgroup (MulAut Q)) : Set (MulAut Q)) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro h
    rw [Subgroup.mem_inf, Subgroup.mem_inf, ← Subgroup.mem_normalizer_iff.mp hg h]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, (inner_normal Q).conj_mem h h2 g⟩
    · rintro ⟨h1, h2⟩
      refine ⟨h1, ?_⟩
      have := (inner_normal Q).conj_mem _ h2 g⁻¹
      simpa [mul_assoc] using this
  let φ : Q →* ↥(inner Q) :=
    (MulAut.conj : Q →* MulAut Q).codRestrict (inner Q) fun x => ⟨x, rfl⟩
  have hφ : ∀ g, (φ g : MulAut Q) = MulAut.conj g := fun g => rfl
  let P : Subgroup Q := ((S ⊓ inner Q).subgroupOf (inner Q)).comap φ
  have hmem : ∀ g : Q, g ∈ P ↔ MulAut.conj g ∈ S ⊓ inner Q := fun g => by
    rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf, hφ]
  have hφinj : Function.Injective φ := fun a b hab => hinj (by rw [← hφ a, ← hφ b, hab])
  have hφsurj : Function.Surjective φ := by
    rintro ⟨y, g, rfl⟩
    exact ⟨g, rfl⟩
  have hPsyl : IsSylowTwoOf P ⊤ := by
    refine ⟨le_top, ?_, ?_⟩
    · exact (hSI.2.1.comap_of_injective (inner Q).subtype Subtype.val_injective).comap_of_injective
        φ hφinj
    · have h1 : P.index = ((S ⊓ inner Q).subgroupOf (inner Q)).index :=
        Subgroup.index_comap_of_surjective _ hφsurj
      show ¬ 2 ∣ P.relIndex ⊤
      rw [Subgroup.relIndex_top_right, h1]
      exact hSI.2.2
  have hconj : ∀ (g : MulAut Q) (x : Q), MulAut.conj (g x) = g * MulAut.conj x * g⁻¹ := by
    intro g x
    ext y
    simp [MulAut.conj_apply, map_mul, map_inv]
  have hgP : ∀ g ∈ Subgroup.normalizer (S : Set (MulAut Q)), ∀ x ∈ P, g x ∈ P := by
    intro g hg x hx
    rw [hmem] at hx ⊢
    rw [hconj]
    exact (Subgroup.mem_normalizer_iff.mp (hNI g hg) _).mp hx
  let α : MulAut ↥P :=
    { toFun := fun x => ⟨d (x : Q), hgP d hdN x x.2⟩
      invFun := fun x => ⟨d⁻¹ (x : Q), hgP d⁻¹ (Subgroup.inv_mem _ hdN) x x.2⟩
      left_inv := fun x => Subtype.ext (by simp)
      right_inv := fun x => Subtype.ext (by simp)
      map_mul' := fun x y => Subtype.ext (map_mul d (x : Q) (y : Q)) }
  have hαpow : ∀ k : ℕ, ∀ x : ↥P, (((α ^ k) x : ↥P) : Q) = (d ^ k) (x : Q) := by
    intro k
    induction k with
    | zero => intro x; simp
    | succ k ih =>
      intro x
      rw [pow_succ', MulAut.mul_apply, pow_succ', MulAut.mul_apply, ← ih x]
      rfl
  have hα1 : α = 1 := by
    obtain ⟨k, hk⟩ := hAut P hPsyl α
    have hm : α ^ orderOf d = 1 := by
      ext x
      rw [hαpow, hdm]
      rfl
    have h1 := orderOf_dvd_of_pow_eq_one hk
    have h2 := orderOf_dvd_of_pow_eq_one hm
    have hcop : Nat.Coprime (2 ^ k) (orderOf d) :=
      Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hodd)
    exact orderOf_eq_one_iff.mp ((Nat.Coprime.coprime_dvd_left h1 hcop).eq_one_of_dvd h2)
  have hfix : ∀ x ∈ P, d x = x := fun x hx => by
    have := congrArg (fun β : MulAut ↥P => ((β ⟨x, hx⟩ : ↥P) : Q)) hα1
    exact this
  have hcentR : ∀ r ∈ S ⊓ inner Q, d * r = r * d := by
    intro r hr
    obtain ⟨x, rfl⟩ := (Subgroup.mem_inf.mp hr).2
    have hxP : x ∈ P := (hmem x).mpr hr
    have e1 := hconj d x
    rw [hfix x hxP] at e1
    calc d * MulAut.conj x = d * MulAut.conj x * d⁻¹ * d := by group
      _ = MulAut.conj x * d := by rw [← e1]
  set π : MulAut Q →* Outer Q := QuotientGroup.mk' (inner Q) with hπ
  have hπker : ∀ g, π g = 1 ↔ g ∈ (inner Q : Subgroup (MulAut Q)) := fun g =>
    QuotientGroup.eq_one_iff g
  let H : Subgroup (Outer Q) := S.map π
  have hH2 : IsPGroup 2 H := hS.2.1.map π
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp hH2
  have hHdvd : 2 ^ a ∣ Nat.card (Outer Q) := ha ▸ Subgroup.card_subgroup_dvd_card H
  have ha1 : a ≤ 1 := by
    by_contra h
    exact hout (dvd_trans (pow_dvd_pow 2 (by omega : 2 ≤ a)) hHdvd)
  have huniq : ∀ x ∈ H, ∀ y ∈ H, x ≠ 1 → y ≠ 1 → x = y := by
    intro x hx y hy hx1 hy1
    have hnt : Nontrivial H := ⟨⟨1, ⟨x, hx⟩, fun h => hx1 (congrArg Subtype.val h).symm⟩⟩
    have h1 : 1 < Nat.card H := Finite.one_lt_card
    have h2 : Nat.card H = 2 := by
      rw [ha] at h1 ⊢
      interval_cases a <;> simp_all
    obtain ⟨z, -, hz⟩ := (Nat.card_eq_two_iff' (1 : H)).mp h2
    have e1 := hz ⟨x, hx⟩ (fun h => hx1 (congrArg Subtype.val h))
    have e2 := hz ⟨y, hy⟩ (fun h => hy1 (congrArg Subtype.val h))
    exact congrArg Subtype.val (e1.trans e2.symm)
  by_cases hsI : s ∈ (inner Q : Subgroup (MulAut Q))
  · exact hcentR s (Subgroup.mem_inf.mpr ⟨hs, hsI⟩)
  · have htS : d * s * d⁻¹ ∈ S := (Subgroup.mem_normalizer_iff.mp hdN s).mp hs
    have htI : d * s * d⁻¹ ∉ (inner Q : Subgroup (MulAut Q)) := fun h => hsI (by
      have := (inner_normal Q).conj_mem _ h d⁻¹
      simpa [mul_assoc] using this)
    have heq : π s = π (d * s * d⁻¹) :=
      huniq _ ⟨s, hs, rfl⟩ _ ⟨_, htS, rfl⟩ (fun h => hsI ((hπker s).mp h))
        (fun h => htI ((hπker _).mp h))
    set z := s⁻¹ * (d * s * d⁻¹) with hz
    have hzI : z ∈ (inner Q : Subgroup (MulAut Q)) := by
      rw [← hπker, hz, map_mul, map_inv, ← heq, inv_mul_cancel]
    have hzS : z ∈ S := S.mul_mem (S.inv_mem hs) htS
    have hdz : d * z = z * d := hcentR z (Subgroup.mem_inf.mpr ⟨hzS, hzI⟩)
    have hpow : ∀ k : ℕ, d ^ k * s * (d ^ k)⁻¹ = s * z ^ k := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        have e1 : d * s * d⁻¹ = s * z := by rw [hz]; group
        have e2 : d * z ^ k * d⁻¹ = z ^ k := by
          rw [(Commute.pow_right hdz k).eq]
          group
        calc d ^ (k + 1) * s * (d ^ (k + 1))⁻¹ = d * (d ^ k * s * (d ^ k)⁻¹) * d⁻¹ := by group
          _ = d * (s * z ^ k) * d⁻¹ := by rw [ih]
          _ = (d * s * d⁻¹) * (d * z ^ k * d⁻¹) := by group
          _ = s * z * z ^ k := by rw [e1, e2]
          _ = s * z ^ (k + 1) := by group
    have hzm : z ^ orderOf d = 1 := by
      have := hpow (orderOf d)
      rw [hdm, one_mul, inv_one, mul_one] at this
      exact (mul_eq_left.mp this.symm)
    obtain ⟨j, hj⟩ := hS.2.1 ⟨z, hzS⟩
    have hz2 : z ^ 2 ^ j = 1 := by simpa using congrArg Subtype.val hj
    have hcop : Nat.Coprime (2 ^ j) (orderOf d) :=
      Nat.Coprime.pow_left j (Nat.coprime_two_left.mpr hodd)
    have hz1 : z = 1 := orderOf_eq_one_iff.mp ((Nat.Coprime.coprime_dvd_left
      (orderOf_dvd_of_pow_eq_one hz2) hcop).eq_one_of_dvd (orderOf_dvd_of_pow_eq_one hzm))
    have : d * s * d⁻¹ = s := by
      have := congrArg (fun w => s * w) hz1
      simp only [hz, mul_one] at this
      simpa [mul_assoc] using this
    calc d * s = d * s * d⁻¹ * d := by group
      _ = s * d := by rw [this]

@[expose] def U35SylowSemidihedral : Prop :=
  ∀ (K : Type) [Field K] [Finite K], Nat.card K = (5 ^ 1) ^ 2 →
    ∃ T : Sylow 2 (StatedProj (StatedSU 3 (5 ^ 1) K)),
      Nonempty (↥(T : Subgroup (StatedProj (StatedSU 3 (5 ^ 1) K))) ≃*
        CFSG.Open.SemidihedralGroup 4)

end CFSG.Quasithin.H13.KGAutSyl
