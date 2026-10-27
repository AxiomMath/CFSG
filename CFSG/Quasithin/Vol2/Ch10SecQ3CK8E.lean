module

public import CFSG.Quasithin.Vol2.Ch10SecQ3CK8C
public import CFSG.Quasithin.Background.FFC4Real
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB.C11AmS.K8

open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin

variable {V : Type} [CommGroup V] {L : Subgroup (MulAut V)}

theorem le_eight_of_dvd {n : ℕ} (hd : n ∣ 16) (hlt : n < 16) : n ≤ 8 := by
  have h16 : (16 : ℕ) = 2 ^ 4 := by norm_num
  rw [h16] at hd
  obtain ⟨i, hi, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hd
  interval_cases i <;> simp_all

theorem card_of_a7Four_bot {U : Subgroup V} (h : A7Four L U ⊥) : Nat.card ↥U = 16 := by
  obtain ⟨α, π, -, -, -, -, -, -, -, β, hβs, hβk, -⟩ := h
  have hinj : Function.Injective β := by
    rw [injective_iff_map_eq_one]
    intro u hu
    have := (hβk u).1 hu
    rw [Subgroup.mem_bot] at this
    exact Subtype.ext this
  rw [Nat.card_congr (Equiv.ofBijective β ⟨hinj, hβs⟩)]
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup
    ((FFModel.a7Four α).ker.subgroupOf (FFModel.a7Four α).sec)
  have h2 : (FFModel.a7Four α).ker.subgroupOf (FFModel.a7Four α).sec = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx
    rw [Subgroup.mem_bot]
    exact Subtype.ext hx
  have h2' : Nat.card ↥((FFModel.a7Four α).ker.subgroupOf (FFModel.a7Four α).sec) = 1 := by
    rw [h2, Subgroup.card_bot]
  rw [h2', mul_one] at h1
  rw [← h1]
  have h3 : (FFModel.a7Four α).sec = ⊤ := rfl
  rw [h3, Subgroup.card_top]
  change Nat.card (Fin 4 → ZMod 2) = 16
  rw [Nat.card_fun, Nat.card_zmod, Nat.card_fin]
  norm_num

theorem a7Four_fix_le [Finite V] (h : A7Four L (commV L) ⊥) (hdir : commV L ⊔ fixV L = ⊤)
    {R : Subgroup (MulAut V)} (hRL : R ≤ L) (hR : R ≠ ⊥) :
    Nat.card ↥(commV L ⊓ fixV R) ≤ 8 := by
  have h16 := card_of_a7Four_bot h
  have hlt : commV L ⊓ fixV R < commV L := by
    refine lt_of_le_of_ne inf_le_left fun heq => hR ?_
    have hle : commV L ≤ fixV R := heq ▸ inf_le_right
    have hL : fixV L ≤ fixV R := fun v hv r hr => hv r (hRL hr)
    have htop : (⊤ : Subgroup V) ≤ fixV R := hdir ▸ sup_le hle hL
    rw [eq_bot_iff]
    intro r hr
    rw [Subgroup.mem_bot]
    ext v
    exact htop (Subgroup.mem_top v) r hr
  have hd : Nat.card ↥(commV L ⊓ fixV R) ∣ 16 :=
    h16 ▸ Subgroup.card_dvd_of_le inf_le_left
  have hl : Nat.card ↥(commV L ⊓ fixV R) < 16 := h16 ▸ Subgroup.card_lt_of_lt hlt
  exact le_eight_of_dvd hd hl

theorem dnZ_seven : Subgroup.zpowers (G6.allOnes 7) ⊓ G6.coreMod 7 = ⊥ := by
  have h := Explicit.card_dnZ (n := 7) (by norm_num)
  rw [ite_eq_right_iff.mpr (fun h7 => absurd h7 (by decide))] at h
  exact Subgroup.card_eq_one.mp h

theorem alt7_fix_le {U : Subgroup V} (h : AlternatingNatural L U ⊥ 7)
    {R : Subgroup (MulAut V)} (hRL : R ≤ L) (hR2 : IsPGroup 2 R) (h4 : 4 ≤ Nat.card R) :
    Nat.card ↥(U ⊓ fixV R) ≤ 8 := by
  obtain ⟨π₀, hπ₀⟩ := h
  let π : ↥(alternatingGroup (Fin 7)) →* ↥L := π₀
  have hπ : (FFModel.altDn 7).RealizesVia L U ⊥ π := hπ₀
  have hinj : Function.Injective π :=
    FFC.injective_of_faithful_sec (FFC.altDn_faithful (by norm_num)) hπ
  obtain ⟨hsurj, -, -, -, -, -, -, β₀, -, hβk, hβe⟩ := hπ
  let K : Subgroup ↥(G6.coreMod 7) :=
    (Subgroup.zpowers (G6.allOnes 7) ⊓ G6.coreMod 7).subgroupOf (G6.coreMod 7)
  let β : ↥U →* ↥(G6.coreMod 7) ⧸ K := β₀
  have hK : K = ⊥ := by
    show (Subgroup.zpowers (G6.allOnes 7) ⊓ G6.coreMod 7).subgroupOf (G6.coreMod 7) = ⊥
    rw [dnZ_seven, Subgroup.bot_subgroupOf]
  have hker : ∀ a b : ↥(G6.coreMod 7), (QuotientGroup.mk a : ↥(G6.coreMod 7) ⧸ K) =
      QuotientGroup.mk b → a = b := by
    intro a b hab
    rw [QuotientGroup.eq, hK, Subgroup.mem_bot] at hab
    exact inv_mul_eq_one.mp hab
  set P₀ : Subgroup ↥(alternatingGroup (Fin 7)) := (R.subgroupOf L).comap π with hP₀
  set P : Subgroup (Equiv.Perm (Fin 7)) := P₀.map (alternatingGroup (Fin 7)).subtype with hP
  have hPA : P ≤ alternatingGroup (Fin 7) := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hR2' : IsPGroup 2 ↥(R.subgroupOf L) :=
    hR2.of_equiv (Subgroup.subgroupOfEquivOfLe hRL).symm
  have hP2 : IsPGroup 2 ↥P := (hR2'.comap_of_injective π hinj).map _
  have hcard : Nat.card ↥P = Nat.card ↥R := by
    rw [hP, Subgroup.card_map_of_injective (Subgroup.subtype_injective _)]
    have hm : P₀.map π = R.subgroupOf L := Subgroup.map_comap_eq_self_of_surjective hsurj _
    rw [← Subgroup.card_map_of_injective hinj, hm]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRL).toEquiv
  have hfix : ∀ u : ↥(U ⊓ fixV R), ∀ σ ∈ P, ∀ i,
      Multiplicative.toAdd ((β ⟨u, u.2.1⟩).out : G6.PermMod 7) (σ⁻¹ i) =
        Multiplicative.toAdd ((β ⟨u, u.2.1⟩).out : G6.PermMod 7) i := by
    intro u σ hσ i
    obtain ⟨γ, hγ, rfl⟩ := hσ
    have hγR : ((π γ : ↥L) : MulAut V) ∈ R := hγ
    have hu : ((π γ : ↥L) : MulAut V) (u : V) = u := u.2.2 _ hγR
    have hmem : ((π γ : ↥L) : MulAut V) (u : V) ∈ U := by rw [hu]; exact u.2.1
    set m : ↥(G6.coreMod 7) := (β ⟨u, u.2.1⟩).out with hm
    have hm' : G6.permAct 7 (γ : Equiv.Perm (Fin 7)) (m : G6.PermMod 7) ∈ G6.coreMod 7 :=
      G6.permAct_mem_coreMod _ m.2
    have he := hβe γ ⟨u, u.2.1⟩ m hmem hm' (QuotientGroup.out_eq' _).symm
    have hval : (⟨((π γ : ↥L) : MulAut V) (u : V), hmem⟩ : ↥U) = ⟨u, u.2.1⟩ := Subtype.ext hu
    have he' : (QuotientGroup.mk m : ↥(G6.coreMod 7) ⧸ K) =
        QuotientGroup.mk ⟨G6.permAct 7 (γ : Equiv.Perm (Fin 7)) (m : G6.PermMod 7), hm'⟩ := by
      have h1 : β ⟨((π γ : ↥L) : MulAut V) (u : V), hmem⟩ = β ⟨u, u.2.1⟩ := by rw [hval]
      have hmk : (QuotientGroup.mk m : ↥(G6.coreMod 7) ⧸ K) = β ⟨u, u.2.1⟩ :=
        QuotientGroup.out_eq' _
      rw [hmk, ← h1]
      exact he
    have h2 := hker _ _ he'
    have h3 := congrArg (fun z : ↥(G6.coreMod 7) => Multiplicative.toAdd (z : G6.PermMod 7) i) h2
    simp only at h3
    rw [h3, G6.permAct_apply]
    rfl
  let E := {x : Fin 7 → ZMod 2 // (∀ σ ∈ P, ∀ i, x (σ⁻¹ i) = x i) ∧ ∑ i, x i = 0}
  let Ψ : ↥(U ⊓ fixV R) → E := fun u =>
    ⟨Multiplicative.toAdd ((β ⟨u, u.2.1⟩).out : G6.PermMod 7), hfix u,
      ((β ⟨u, u.2.1⟩).out).2⟩
  have hΨ : Function.Injective Ψ := by
    intro u v huv
    have h0 := congrArg Subtype.val huv
    have h1 : (β ⟨u, u.2.1⟩).out = (β ⟨v, v.2.1⟩).out :=
      Subtype.ext (Multiplicative.toAdd.injective h0)
    have h2 : β ⟨u, u.2.1⟩ = β ⟨v, v.2.1⟩ := by
      rw [← QuotientGroup.out_eq' (β ⟨u, u.2.1⟩), ← QuotientGroup.out_eq' (β ⟨v, v.2.1⟩), h1]
    have h3 : β₀ (⟨u, u.2.1⟩ * (⟨v, v.2.1⟩ : ↥U)⁻¹) = 1 := by
      show β (⟨u, u.2.1⟩ * (⟨v, v.2.1⟩ : ↥U)⁻¹) = 1
      rw [map_mul, map_inv, h2, mul_inv_cancel]
    have h4 := (hβk _).1 h3
    rw [Subgroup.mem_bot] at h4
    have h5 : (u : V) * (v : V)⁻¹ = 1 := h4
    exact Subtype.ext (mul_inv_eq_one.mp h5)
  calc Nat.card ↥(U ⊓ fixV R) ≤ Nat.card E := Nat.card_le_card_of_injective Ψ hΨ
    _ ≤ 8 := card_fixVec_even_le hP2 hPA (hcard ▸ h4)

end CFSG.Quasithin.Vol2.Ch10.SecB.C11AmS.K8
