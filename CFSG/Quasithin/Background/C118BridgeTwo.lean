module

public import CFSG.Quasithin.Background.C118S3

public section

namespace CFSG.Quasithin

open Subgroup CFSG CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.Campbell

section Classes

variable {G : Type*} [Group G]

structure InClassG2 (H S : Subgroup G) : Prop where
  cls : InClassG H S
  two : ∃ n : ℕ, 2 ≤ n ∧
    IsNatL2Section (fstarPre H (VZ S H)) (Subgroup.centralizer (VZ S H : Set G))
      ⁅VZ S H, fstarPre H (VZ S H)⁆
      (⁅VZ S H, fstarPre H (VZ S H)⁆ ⊓ Subgroup.centralizer (fstarPre H (VZ S H) : Set G)) n

@[expose] def classG2 : ClassPred := fun H S => InClassG2 H S

theorem InClassG.one_or_two {H S : Subgroup G} (h : InClassG H S) :
    InClassG1 H S ∨ InClassG2 H S := by
  obtain ⟨n, hn, hsec⟩ := h.natural
  rcases Nat.lt_or_ge n 2 with h1 | h2
  · left
    have : n = 1 := by omega
    subst this
    exact ⟨h, hsec⟩
  · right
    exact ⟨h, n, h2, hsec⟩

end Classes

section Bridge

@[expose] def NoOuterFact : Prop :=
  ∀ (Ω : Type) [Group Ω] [Finite Ω] (B H : Subgroup Ω), baum B = B → InClassG2 H B →
    B ≤ fstarPre H (VZ B H)

theorem classSeedBridgeOne : ClassSeedBridgeFor classG1 := fun Ω _ _ B H hbaum hcl => by
  obtain ⟨d⟩ := exists_natData hcl.one
  exact exists_seed_of_natOneData hcl.cls.isSylow hcl.cls.charTwo hcl.cls.minParabolic hbaum d

theorem classSeedBridgeTwo_of_noOuter (hno : NoOuterFact) : ClassSeedBridgeFor classG2 := by
  intro Ω _ _ B H hbaum hcl
  obtain ⟨n, hn2, hsec⟩ := hcl.two
  obtain ⟨d⟩ := exists_natData (B := B) (H := H) hsec
  have hB := hcl.cls.isSylow
  have hchar := hcl.cls.charTwo
  obtain ⟨M, hMP⟩ := exists_minParabolic hB hcl.cls.minParabolic
  have hBK : B ≤ clK B H := hno Ω B H hbaum hcl
  have hKH : clK B H = H :=
    normal_sylow_eq hMP hBK (clK_le B H) (H_le_normalizer_clK B H)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hchp : CharP d.F 2 := charP_of_card_eq_prime_pow d.hcard
  have hfin : Finite d.F := Finite.of_fintype d.F
  let e : ↥H ≃* ↥(clK B H) := MulEquiv.subgroupCongr hKH.symm
  let ρ : ↥H →* Matrix.SpecialLinearGroup (Fin 2) d.F := d.α.comp e.toMonoidHom
  have hρ : IsRhoFor d ρ := by
    intro g u v hv
    exact d.hβ_equiv (e g) u v (by simpa [e] using hv)
  have h4 : ∃ s : Finset d.F, s.card = 4 := by
    have h4' : 4 ≤ (Finset.univ : Finset d.F).card := by
      rw [Finset.card_univ, d.hcard]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
    obtain ⟨t, -, ht⟩ := Finset.exists_subset_card_eq h4'
    exact ⟨t, ht⟩
  have htop : (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) d.F)) ≠ ⊥ := by
    intro h
    apply not_commutative_sl2 (F := d.F)
    intro a b
    have ha : a = 1 := Subgroup.mem_bot.mp (h ▸ Subgroup.mem_top a)
    have hb : b = 1 := Subgroup.mem_bot.mp (h ▸ Subgroup.mem_top b)
    rw [ha, hb]
  have hcomm : commutator (Matrix.SpecialLinearGroup (Fin 2) d.F) = ⊤ :=
    commutator_top_sl2_eq_top h4 ⊤ htop
  have hαsurj : Function.Surjective d.α := by
    apply MonoidHom.range_eq_top.mp
    rw [d.hα_range, hcomm]
  have hsurj : Function.Surjective ρ := fun x => by
    obtain ⟨k, hk⟩ := hαsurj x
    exact ⟨e.symm k, by simp [ρ, hk]⟩
  have hHV : ¬ H ≤ Subgroup.centralizer (clV B H : Set Ω) := by
    intro hle
    obtain ⟨g, hg⟩ : ∃ g : ↥H, ρ g ≠ 1 := by
      by_contra hall
      push Not at hall
      apply not_commutative_sl2 (F := d.F)
      intro a b
      obtain ⟨ga, rfl⟩ := hsurj a
      obtain ⟨gb, rfl⟩ := hsurj b
      rw [hall ga, hall gb]
    refine hg (hρ.eq_one_of_centralizes g fun u hu => ?_)
    have := Subgroup.mem_centralizer_iff.mp (hle g.2) u (clW1_le_clV B H hu)
    exact this.symm
  have hred : IsTwoReducedIn H (clV B H) :=
    isTwoReducedIn_conjClosure_of_sylowIn hB.1 hB.2.1 hB.2.2 hchar le_rfl
  have hker : ρ.ker.map H.subtype ≤ kerIn M H := by
    rintro _ ⟨y, hy, rfl⟩
    have h1 : e y ∈ d.α.ker := hy
    rw [d.hα_ker, Subgroup.mem_subgroupOf] at h1
    exact hMP.inf_centralizer_le_kerIn hred hHV ⟨y.2, h1⟩
  have hW0 : ∀ x : ↥H, (x : Ω) ∈ clW0 B H → x ∈ Subgroup.center ↥H := by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro g
    have hgK : (g : Ω) ∈ clK B H := by
      rw [hKH]
      exact g.2
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hx.2 (g : Ω) hgK)
  obtain ⟨S, ψ, hS, hseed⟩ := isSeed_of_rho (by omega : 1 ≤ n) hB hchar hMP hbaum d ρ hρ hsurj
    hker hW0
  obtain ⟨ψE, hE, -⟩ := hseed.toEcore
  exact ⟨d.F, inferInstance, hfin, S, ρ, ψE, hS, hE⟩

theorem classSeedBridge_of_noOuter (hno : NoOuterFact) : ClassSeedBridge := by
  intro Ω _ _ B H hbaum hcl
  rcases hcl.one_or_two with h1 | h2
  · exact classSeedBridgeOne Ω B H hbaum h1
  · exact classSeedBridgeTwo_of_noOuter hno Ω B H hbaum h2

theorem theoremC118_of_noOuter (hno : NoOuterFact) : TheoremC118 :=
  theoremC118_of_bridge (classSeedBridge_of_noOuter hno)

end Bridge

end CFSG.Quasithin
