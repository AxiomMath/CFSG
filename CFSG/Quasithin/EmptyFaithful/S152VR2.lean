module

public import CFSG.Quasithin.EmptyFaithful.S152VR1
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Background.A3StructureDefs

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Blueprint

namespace S152V

@[expose] def Rank2 (X : Type*) [Group X] : Prop :=
  ∃ E : Subgroup X, IsMulCommutative E ∧ (∀ x ∈ E, x ^ 3 = 1) ∧ Nat.card E = 9

theorem rank2_lift {X : Type*} [Group X] [Finite X] (N : Subgroup X) [N.Normal]
    (hN : ¬ 3 ∣ Nat.card N) (h : Rank2 (X ⧸ N)) : Rank2 X := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨E₀, hE₀c, hE₀e, hE₀card⟩ := h
  let Ê : Subgroup X := E₀.comap (QuotientGroup.mk' N)
  have hÊcard : Nat.card Ê = Nat.card N * 9 := by
    have h := QuotientGroup.card_preimage_mk N (E₀ : Set (X ⧸ N))
    have e1 : Nat.card Ê = Nat.card ↑(QuotientGroup.mk ⁻¹' (E₀ : Set (X ⧸ N))) := rfl
    rw [e1, h]
    show Nat.card N * Nat.card ↥E₀ = _
    rw [hE₀card]
  obtain ⟨S, hS⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥Ê) 3 (n := 2)
    (by rw [hÊcard]; exact Dvd.intro_left _ rfl)
  let E : Subgroup X := S.map Ê.subtype
  have hEcard : Nat.card E = 9 := by
    rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective _), hS]
    norm_num
  have hEÊ : E ≤ Ê := by
    rintro _ ⟨s, -, rfl⟩
    exact s.2
  have hcop : Nat.Coprime (Nat.card E) (Nat.card N) := by
    rw [hEcard]
    exact Nat.Coprime.pow_left 2 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hN)
  have hEN : ∀ x ∈ E, x ∈ N → x = 1 := by
    intro x hx hxN
    have h1 : x ^ Nat.card E = 1 := by
      have := pow_card_eq_one' (G := ↥E) (x := (⟨x, hx⟩ : ↥E))
      exact congrArg Subtype.val this
    have h2 : x ^ Nat.card N = 1 := by
      have := pow_card_eq_one' (G := ↥N) (x := (⟨x, hxN⟩ : ↥N))
      exact congrArg Subtype.val this
    have := pow_gcd_eq_one.2 ⟨h1, h2⟩
    rwa [hcop.gcd_eq_one, pow_one] at this
  refine ⟨E, ?_, ?_, hEcard⟩
  · refine ⟨⟨fun a b => ?_⟩⟩
    apply Subtype.ext
    show (a : X) * b = b * a
    have ha := hEÊ a.2
    have hb := hEÊ b.2
    have hc : (a : X) * b * ((b : X) * a)⁻¹ ∈ E := E.mul_mem (E.mul_mem a.2 b.2)
      (E.inv_mem (E.mul_mem b.2 a.2))
    have hN' : (a : X) * b * ((b : X) * a)⁻¹ ∈ N := by
      rw [← QuotientGroup.eq_one_iff]
      have hca := hE₀c.is_comm.comm ⟨QuotientGroup.mk (a : X), ha⟩ ⟨QuotientGroup.mk (b : X), hb⟩
      have := congrArg Subtype.val hca
      simp only [Subgroup.coe_mul] at this
      simp [this]
    have h1 := hEN _ hc hN'
    exact mul_inv_eq_one.1 h1
  · intro x hx
    have hxÊ := hEÊ hx
    have h3 : (x ^ 3) ∈ N := by
      rw [← QuotientGroup.eq_one_iff]
      have := hE₀e _ hxÊ
      simpa using this
    exact hEN _ (E.pow_mem hx 3) h3

theorem card_le_nine_of_sqtk {G : Type} [Group G] [Finite G] {I : Subgroup G} (hI : SQTKGroup ↥I)
    (E : Subgroup G) (hEI : E ≤ I) (hEc : IsMulCommutative E) (hE3 : ∀ x ∈ E, x ^ 3 = 1) :
    Nat.card E ≤ 9 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp : IsPGroup 3 E := fun x => ⟨1, Subtype.ext (by simpa using hE3 x.1 x.2)⟩
  obtain ⟨k, hk⟩ := hp.exists_card_eq
  let E' : Subgroup ↥I := E.subgroupOf I
  have hE'card : Nat.card E' = 3 ^ k :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEI).toEquiv).trans hk
  have hE'el : CFSG.Assembly.IsElemAbelian 3 E' := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
    · apply Subtype.ext
      apply Subtype.ext
      have ha : ((a : ↥I) : G) ∈ E := a.2
      have hb : ((b : ↥I) : G) ∈ E := b.2
      have := hEc.is_comm.comm ⟨_, ha⟩ ⟨_, hb⟩
      exact congrArg (fun t : ↥E => (t : G)) this
    · apply Subtype.ext
      have hx' : ((x : ↥I) : G) ∈ E := hx
      simpa using hE3 _ hx'
  have hle : k ≤ CFSG.Assembly.pRank 3 (⊤ : Subgroup ↥I) := by
    refine le_csSup ⟨Nat.card ↥I, ?_⟩ ⟨E', le_top, hE'el, hE'card⟩
    rintro r ⟨B, -, -, hB⟩
    calc r ≤ 3 ^ r := (Nat.lt_pow_self (by norm_num)).le
      _ = Nat.card B := hB.symm
      _ ≤ Nat.card ↥I := Subgroup.card_le_card_group B
  have h2 := hI.1 3 Nat.prime_three (by norm_num)
  rw [hk]
  calc 3 ^ k ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) (hle.trans h2)
    _ = 9 := by norm_num

theorem centralizer_trivial_of_rank {G : Type} [Group G] [Finite G] {I L P : Subgroup G} (hLI : L ≤ I)
    (hPI : P ≤ I) (hE : Rank2 ↥L) (hI : SQTKGroup ↥I)
    (hZ : ∀ y ∈ L, (∀ w ∈ L, w * y = y * w) → ∃ k : ℕ, y ^ (2 ^ k) = 1)
    (hexp : ∀ x ∈ P, x ^ 3 = 1) : ∀ x ∈ P, (∀ y ∈ L, x * y = y * x) → x = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro x hx hcomm
  by_contra hx1
  obtain ⟨E0, hE0c, hE03, hE09⟩ := hE
  let E : Subgroup G := E0.map L.subtype
  have hEL : E ≤ L := by
    rintro _ ⟨s, -, rfl⟩
    exact s.2
  have hEI : E ≤ I := hEL.trans hLI
  have hEcard : Nat.card E = 9 := by
    rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective _), hE09]
  have hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    have := hE0c.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩
    have h2 := congrArg (fun t : ↥E0 => ((t : ↥L) : G)) this
    simpa using h2
  have hE3 : ∀ a ∈ E, a ^ 3 = 1 := by
    rintro _ ⟨a, ha, rfl⟩
    have h2 := congrArg Subtype.val (hE03 a ha)
    simpa using h2
  have hxL : x ∉ L := by
    intro hxL
    obtain ⟨k, hk⟩ := hZ x hxL (fun w hw => (hcomm w hw).symm)
    have h2 : x ^ Nat.gcd 3 (2 ^ k) = 1 := pow_gcd_eq_one.2 ⟨hexp x hx, hk⟩
    have h3 : Nat.gcd 3 (2 ^ k) = 1 := Nat.Coprime.pow_right k (by norm_num)
    rw [h3, pow_one] at h2
    exact hx1 h2
  have hcommset : ((E : Set G) ∪ {x}).Pairwise Commute := by
    intro a ha b hb _
    rcases ha with ha | ha <;> rcases hb with hb | hb
    · exact hEc a ha b hb
    · rw [Set.mem_singleton_iff] at hb
      rw [hb]
      exact (hcomm a (hEL ha)).symm
    · rw [Set.mem_singleton_iff] at ha
      rw [ha]
      exact hcomm b (hEL hb)
    · rw [Set.mem_singleton_iff] at ha hb
      rw [ha, hb]
  let E' : Subgroup G := Subgroup.closure ((E : Set G) ∪ {x})
  have hE'c : IsMulCommutative E' := Subgroup.isMulCommutative_closure hcommset
  have hE'comm : ∀ a ∈ E', ∀ b ∈ E', a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hE'c.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hE'3 : ∀ g ∈ E', g ^ 3 = 1 := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem y hy =>
      rcases hy with hy | hy
      · exact hE3 y hy
      · rw [Set.mem_singleton_iff] at hy
        rw [hy]
        exact hexp x hx
    | one => simp
    | mul a b ha hb iha ihb =>
      rw [(show Commute a b from hE'comm a ha b hb).mul_pow, iha, ihb, one_mul]
    | inv a ha iha => rw [inv_pow, iha, inv_one]
  have hxE' : x ∈ E' := Subgroup.subset_closure (Or.inr rfl)
  have hEE' : E ≤ E' := fun a ha => Subgroup.subset_closure (Or.inl ha)
  have hE'I : E' ≤ I := by
    refine (Subgroup.closure_le I).2 ?_
    rintro a (ha | ha)
    · exact hEI ha
    · rw [Set.mem_singleton_iff] at ha
      rw [ha]
      exact hPI hx
  have hp : IsPGroup 3 E' := fun g => ⟨1, Subtype.ext (by simpa using hE'3 g.1 g.2)⟩
  obtain ⟨n, hn⟩ := hp.exists_card_eq
  have hdvd : 9 ∣ Nat.card E' := hEcard ▸ Subgroup.card_dvd_of_le hEE'
  have hne : Nat.card E' ≠ 9 := by
    intro h9
    have hEeq : E = E' := Subgroup.eq_of_le_of_card_ge hEE' (by rw [hEcard, h9])
    exact hxL (hEL (hEeq ▸ hxE'))
  have h27 : 27 ≤ Nat.card E' := by
    rw [hn] at hdvd hne ⊢
    rcases Nat.lt_or_ge n 3 with h | h
    · interval_cases n
      · norm_num at hdvd
      · norm_num at hdvd
      · exact absurd rfl hne
    · calc 27 = 3 ^ 3 := by norm_num
        _ ≤ 3 ^ n := Nat.pow_le_pow_right (by norm_num) h
  have := card_le_nine_of_sqtk hI E' hE'I hE'c hE'3
  omega

theorem exists_fixedSubgroup_of_config {G : Type} [Group G] {L P : Subgroup G} {z : G}
    (hperf : Group.IsPerfect ↥L) {Γ : Type} [Group Γ] (ψ : (↥L ⧸ Subgroup.center ↥L) ≃* Γ)
    (hZΓ : Subgroup.center Γ = ⊥) (hOut : ∀ α : MulAut Γ, α ^ 3 = 1 → ∃ g : Γ, α = MulAut.conj g)
    (hPN : P ≤ Subgroup.normalizer (L : Set G)) (hz : z ∈ Subgroup.normalizer (L : Set G))
    (hPz : ∀ x ∈ P, x * z = z * x) (hexp : ∀ x ∈ P, x ^ 3 = 1)
    (hfaith : ∀ x ∈ P, (∀ y ∈ L, x * y = y * x) → x = 1) :
    ∃ H : Subgroup Γ, Nat.card H = Nat.card P ∧ (∀ g ∈ H, g ^ 3 = 1) ∧
      ∀ g ∈ H, inducedAut ψ (L.normalizerMonoidHom ⟨z⁻¹, Subgroup.inv_mem _ hz⟩) g = g := by
  let ρ : ↥P →* MulAut ↥L := L.normalizerMonoidHom.comp (Subgroup.inclusion hPN)
  refine exists_fixed_subgroup hperf ψ hZΓ hOut (E := ↥P)
    (fun e => Subtype.ext (by simpa using hexp e.1 e.2)) ρ ?_
    (inducedAut ψ (L.normalizerMonoidHom ⟨z⁻¹, Subgroup.inv_mem _ hz⟩)) ?_
  · rw [injective_iff_map_eq_one]
    intro e he
    apply Subtype.ext
    show (e : G) = 1
    refine hfaith e e.2 fun y hy => ?_
    have h1 := congrArg (fun a : MulAut ↥L => ((a ⟨y, hy⟩ : ↥L) : G)) he
    simp only [ρ, MonoidHom.comp_apply, MulAut.one_apply] at h1
    have h2 : (e : G) * y * (e : G)⁻¹ = y := by
      have := Subgroup.normalizerMonoidHom_apply_apply_coe L (Subgroup.inclusion hPN e) ⟨y, hy⟩
      simpa using this.symm.trans h1
    calc (e : G) * y = ((e : G) * y * (e : G)⁻¹) * (e : G) := by group
      _ = y * e := by rw [h2]
  · intro e
    rw [← map_mul, ← map_mul]
    congr 1
    show L.normalizerMonoidHom (Subgroup.inclusion hPN e) * L.normalizerMonoidHom ⟨z⁻¹, _⟩ =
      L.normalizerMonoidHom ⟨z⁻¹, _⟩ * L.normalizerMonoidHom (Subgroup.inclusion hPN e)
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    show (e : G) * z⁻¹ = z⁻¹ * (e : G)
    have hc : Commute (e : G) z := hPz e e.2
    exact (hc.inv_right).eq

end S152V

end CFSG.Quasithin
