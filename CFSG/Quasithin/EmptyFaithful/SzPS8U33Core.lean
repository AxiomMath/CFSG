module

public import CFSG.Quasithin.EmptyFaithful.SzPS8Ovg
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtC3LocU33

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.H13.U3 CFSG.Quasithin.GoldC3

namespace SzPS8

section Aut

variable {X G : Type*} [Group X] [Group G]

theorem exists_conjAut (ρ : X →* G) (hρ : Function.Injective ρ) (τ : G)
    (h1 : ∀ k ∈ ρ.range, τ * k * τ⁻¹ ∈ ρ.range) (h2 : ∀ k ∈ ρ.range, τ⁻¹ * k * τ ∈ ρ.range) :
    ∃ α : MulAut X, ∀ g, ρ (α g) = τ * ρ g * τ⁻¹ := by
  choose f hf using fun g : X => MonoidHom.mem_range.mp (h1 (ρ g) ⟨g, rfl⟩)
  choose f' hf' using fun g : X => MonoidHom.mem_range.mp (h2 (ρ g) ⟨g, rfl⟩)
  have hl : ∀ g, f' (f g) = g := fun g => hρ (by rw [hf', hf]; group)
  have hr : ∀ g, f (f' g) = g := fun g => hρ (by rw [hf, hf']; group)
  have hm : ∀ g h, f (g * h) = f g * f h := fun g h =>
    hρ (by rw [hf, map_mul, map_mul, hf, hf]; group)
  exact ⟨{ toFun := f, invFun := f', left_inv := hl, right_inv := hr, map_mul' := hm }, hf⟩

end Aut

section Main

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

theorem u33_A_ne_B :
    u33Data.A ≠ u33Data.B := by
  intro h
  have h1 := u33_sup_AB
  rw [← h, sup_idem] at h1
  have h2 := card_u33_A
  rw [h1, Subgroup.card_top, card_u33Pres] at h2
  norm_num at h2

theorem OvgSetting.false_of_u33
    {Γ T0 : Subgroup (V ≃ₗ[ZMod 2] V)} {v : V}
    (S : OvgSetting Γ T0 v) (ρ : U33G →* (V ≃ₗ[ZMod 2] V)) (hρ : Function.Injective ρ)
    (hKΓ : ρ.range ≤ Γ) (hKn : ∀ γ ∈ Γ, ∀ k ∈ ρ.range, γ * k * γ⁻¹ ∈ ρ.range)
    (hidx : ∃ m : ℕ, Nat.card Γ = 2 ^ m * 6048) : False := by
  classical
  have hfin : Finite (V ≃ₗ[ZMod 2] V) :=
    Finite.of_injective (fun e => (e : V → V)) fun _ _ h => LinearEquiv.ext (congrFun h)
  have h2prime : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsimple : IsSimpleGroup U33G := isSimpleGroup_u33Pres
  have hcardU : Nat.card U33G = 6048 := card_u33Pres
  set K : Subgroup (V ≃ₗ[ZMod 2] V) := ρ.range with hK
  have hKcard : Nat.card K = 6048 := by
    rw [hK, ← Nat.card_congr (MonoidHom.ofInjective hρ).toEquiv, hcardU]
  set T : Subgroup (V ≃ₗ[ZMod 2] V) := u33Data.T.map ρ with hT
  have hTcard : Nat.card T = 32 := by rw [hT, Subgroup.card_map_of_injective hρ, u33_card_T]
  have hT2 : IsPGroup 2 T := IsPGroup.of_card (n := 5) (by rw [hTcard]; norm_num)
  have hTK : T ≤ K := Subgroup.map_le_range ρ _
  have hTΓ : T ≤ Γ := hTK.trans hKΓ
  obtain ⟨T1, hT1syl, hTT1⟩ :=
    CFSG.QuasithinUnique.EscapingLocal.exists_isSylowTwoOf_ge hTΓ hT2
  obtain ⟨v', S'⟩ := S.exists_of_sylow hT1syl
  obtain ⟨N, hNΓ, hNn, hN1, hF⟩ := S'.exists_normal
  have hTT1K : T1 ⊓ K = T := by
    have hle : T ≤ T1 ⊓ K := le_inf hTT1 hTK
    have hp : IsPGroup 2 ↥(T1 ⊓ K) := hT1syl.2.1.to_inf_left
    obtain ⟨n, hn⟩ := hp.exists_card_eq
    have hdvd : Nat.card ↥(T1 ⊓ K) ∣ Nat.card K := Subgroup.card_dvd_of_le inf_le_right
    have hle5 : n ≤ 5 := by
      rw [hn, hKcard] at hdvd
      by_contra h
      push Not at h
      have : 2 ^ 6 ∣ 6048 := (pow_dvd_pow 2 h).trans hdvd
      norm_num at this
    have hcard : Nat.card ↥(T1 ⊓ K) ≤ Nat.card T := by
      rw [hn, hTcard]
      calc 2 ^ n ≤ 2 ^ 5 := Nat.pow_le_pow_right (by norm_num) hle5
        _ = 32 := by norm_num
    exact (Subgroup.eq_of_le_of_card_ge hle hcard).symm
  have hKN : K ≤ N := by
    have hnorm : (N.comap ρ).Normal := ⟨fun g hg h => by
      show ρ (h * g * h⁻¹) ∈ N
      rw [map_mul, map_mul, map_inv]
      exact hNn _ (hKΓ ⟨h, rfl⟩) _ hg⟩
    rcases hnorm.eq_bot_or_eq_top with hbot | htop
    · exfalso
      have hNK : ∀ x ∈ N, x ∈ K → x = 1 := by
        rintro _ hx ⟨g, rfl⟩
        have hg : g ∈ N.comap ρ := hx
        rw [hbot, Subgroup.mem_bot] at hg
        rw [hg, map_one]
      have hKg : (K.subgroupOf Γ).Normal := ⟨fun x hx g => by
        have h1 : ((g : V ≃ₗ[ZMod 2] V)) * (x : V ≃ₗ[ZMod 2] V) * (g : V ≃ₗ[ZMod 2] V)⁻¹ ∈ K :=
          hKn _ g.2 _ hx
        exact h1⟩
      have hQcard : Nat.card (↥Γ ⧸ K.subgroupOf Γ) = 2 ^ hidx.choose := by
        have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (K.subgroupOf Γ)
        have h2 : Nat.card (K.subgroupOf Γ) = 6048 := by
          rw [← hKcard]
          exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKΓ).toEquiv
        have h3 : Nat.card Γ = 2 ^ hidx.choose * 6048 := hidx.choose_spec
        rw [h2, h3] at h1
        exact Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 6048) h1.symm
      have hQ2 : IsPGroup 2 (↥Γ ⧸ K.subgroupOf Γ) := IsPGroup.of_card hQcard
      have hNΓn : (N.subgroupOf Γ).Normal := ⟨fun x hx g => by
        have h1 : ((g : V ≃ₗ[ZMod 2] V)) * (x : V ≃ₗ[ZMod 2] V) * (g : V ≃ₗ[ZMod 2] V)⁻¹ ∈ N :=
          hNn _ g.2 _ hx
        exact h1⟩
      have hN2 : IsPGroup 2 ↥(N.subgroupOf Γ) := by
        refine hQ2.of_injective ((QuotientGroup.mk' (K.subgroupOf Γ)).comp
          (N.subgroupOf Γ).subtype) ?_
        rw [injective_iff_map_eq_one]
        intro x hx
        have hx1 : (x : ↥Γ) ∈ K.subgroupOf Γ := (QuotientGroup.eq_one_iff _).mp hx
        have hx2 : ((x : ↥Γ) : V ≃ₗ[ZMod 2] V) = 1 := hNK _ x.2 hx1
        exact Subtype.ext (Subtype.ext hx2)
      let P : Sylow 2 ↥Γ := IsPGroup.toSylow (P := T1.subgroupOf Γ)
        (hT1syl.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hT1syl.1).symm) hT1syl.2.2
      have hNP : N.subgroupOf Γ ≤ T1.subgroupOf Γ := hN2.le_sylow_of_normal P
      have hNT1 : N ≤ T1 := fun x hx => hNP (show (⟨x, hNΓ hx⟩ : ↥Γ) ∈ N.subgroupOf Γ from hx)
      exact S'.false_of_fixes hNn hN1 fun α hα => S'.fix α (hNT1 hα)
    · rintro _ ⟨g, rfl⟩
      have : g ∈ N.comap ρ := htop ▸ Subgroup.mem_top g
      exact this
  have hnormAB : ∀ τ ∈ T1, (∀ g ∈ u33Data.A, ∃ g' ∈ u33Data.A, τ * ρ g * τ⁻¹ = ρ g') ∧
      (∀ g ∈ u33Data.B, ∃ g' ∈ u33Data.B, τ * ρ g * τ⁻¹ = ρ g') := by
    intro τ hτ
    have hτΓ : τ ∈ Γ := hT1syl.1 hτ
    have h1 : ∀ k ∈ ρ.range, τ * k * τ⁻¹ ∈ ρ.range := hKn τ hτΓ
    have h2 : ∀ k ∈ ρ.range, τ⁻¹ * k * τ ∈ ρ.range := fun k hk => by
      have h := hKn τ⁻¹ (Γ.inv_mem hτΓ) k hk
      rw [inv_inv] at h
      exact h
    obtain ⟨α, hα⟩ := exists_conjAut ρ hρ τ h1 h2
    have hαT : u33Data.T.map α.toMonoidHom = u33Data.T := by
      have hle : u33Data.T.map α.toMonoidHom ≤ u33Data.T := by
        rintro _ ⟨g, hg, rfl⟩
        have hm : ρ (α.toMonoidHom g) ∈ T := by
          rw [← hTT1K]
          refine ⟨?_, ⟨_, rfl⟩⟩
          show ρ (α g) ∈ T1
          rw [hα]
          exact T1.mul_mem (T1.mul_mem hτ (hTT1 ⟨g, hg, rfl⟩)) (T1.inv_mem hτ)
        obtain ⟨g', hg', hg'e⟩ := hm
        have : g' = α.toMonoidHom g := hρ hg'e
        exact this ▸ hg'
      exact Subgroup.eq_of_le_of_card_ge hle
        (by rw [Subgroup.card_map_of_injective α.injective])
    have hαA : u33Data.A.map α.toMonoidHom = u33Data.A := u33_inv α hαT
    have hαB : u33Data.B.map α.toMonoidHom = u33Data.B := by
      have hTB : u33Data.T ≤ u33Data.B.map α.toMonoidHom := by
        calc u33Data.T = u33Data.T.map α.toMonoidHom := hαT.symm
          _ ≤ u33Data.B.map α.toMonoidHom := Subgroup.map_mono u33Data.T_le_B
      have hcardB : Nat.card (u33Data.B.map α.toMonoidHom) = 96 := by
        rw [Subgroup.card_map_of_injective α.injective, card_u33_B]
      rcases u33Data.lattice _ hTB with h | h | h | h
      · rw [h, u33_card_T] at hcardB
        norm_num at hcardB
      · exfalso
        have : u33Data.B = u33Data.A :=
          Subgroup.map_injective (f := α.toMonoidHom) α.injective (h.trans hαA.symm)
        exact u33_A_ne_B this.symm
      · exact h
      · rw [h, Subgroup.card_top, hcardU] at hcardB
        norm_num at hcardB
    refine ⟨fun g hg => ⟨α g, ?_, (hα g).symm⟩, fun g hg => ⟨α g, ?_, (hα g).symm⟩⟩
    · rw [← hαA]
      exact ⟨g, hg, rfl⟩
    · rw [← hαB]
      exact ⟨g, hg, rfl⟩
  have hJ : ∀ H : Subgroup U33G, u33Data.T ≤ H → Nat.card H = 96 →
      (∀ τ ∈ T1, ∀ g ∈ H, ∃ g' ∈ H, τ * ρ g * τ⁻¹ = ρ g') → ∀ α ∈ H.map ρ, α v' = v' := by
    intro H hTH hH96 hnormH
    have hJK : H.map ρ ≤ N := (Subgroup.map_le_range ρ H).trans hKN
    have hJn : ∀ t ∈ T1, ∀ j ∈ H.map ρ, t * j * t⁻¹ ∈ H.map ρ := by
      rintro t ht _ ⟨g, hg, rfl⟩
      obtain ⟨g', hg', he⟩ := hnormH t ht g hg
      exact ⟨g', hg', he.symm⟩
    have hinf : T1 ⊓ H.map ρ = T := by
      apply le_antisymm
      · calc T1 ⊓ H.map ρ ≤ T1 ⊓ K := inf_le_inf_left _ (Subgroup.map_le_range ρ H)
          _ = T := hTT1K
      · exact le_inf hTT1 (Subgroup.map_mono hTH)
    have hidx3 : T1.relIndex (H.map ρ) = 3 := by
      have h := Subgroup.relIndex_mul_card (H := T1) (K := H.map ρ)
      rw [hinf, hTcard, Subgroup.card_map_of_injective hρ, hH96] at h
      omega
    exact hF (H.map ρ) hJK hJn (Or.inl hidx3)
  have hA' := hJ u33Data.A u33Data.T_le_A card_u33_A fun τ hτ => (hnormAB τ hτ).1
  have hB' := hJ u33Data.B u33Data.T_le_B card_u33_B fun τ hτ => (hnormAB τ hτ).2
  have hKfix : ∀ α ∈ K, α v' = v' := by
    have hle : (⊤ : Subgroup U33G) ≤
        (MulAction.stabilizer (V ≃ₗ[ZMod 2] V) v').comap ρ := by
      rw [← u33_sup_AB]
      refine sup_le (fun g hg => ?_) (fun g hg => ?_)
      · exact MulAction.mem_stabilizer_iff.mpr (hA' (ρ g) ⟨g, hg, rfl⟩)
      · exact MulAction.mem_stabilizer_iff.mpr (hB' (ρ g) ⟨g, hg, rfl⟩)
    rintro _ ⟨g, rfl⟩
    exact MulAction.mem_stabilizer_iff.mp (hle (Subgroup.mem_top g))
  have hK1 : K ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hKcard
    norm_num at hKcard
  exact S'.false_of_fixes hKn hK1 hKfix

end Main

end SzPS8

end CFSG.Quasithin
