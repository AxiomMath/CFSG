module

public import CFSG.Quasithin.H13.U3S1347P4E
public import CFSG.Quasithin.H13.U3S1347V

public section

namespace CFSG.Quasithin.H13.U3

open Subgroup Equiv CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.H13.A6 CFSG.LieType.BorelTits
open scoped IsMulCommutative

namespace L32Mod

open CFSG.Quasithin.H6

variable {M : Type} [AddCommGroup M]

theorem fix_three_core {ρ : Γ →* AddMonoid.End M} (h : IsoMod ρ ρCore) {g : Γ} (hg3 : g ^ 3 = 1)
    (hg1 : g ≠ 1) : 16 * Nat.card (Fix ρ {g}) ≤ Nat.card M := by
  obtain ⟨f, hf, hfe⟩ := h
  rw [card_fix_of_iso f hf hfe, card_fix_core_one, ← Nat.card_congr (Equiv.ofBijective f hf),
    card_core]
  have := core_fix_three g hg3 hg1
  omega

theorem fix_three_core_graph {ρ : Γ →* AddMonoid.End M}
    (h : IsoMod (ρ.comp graph.toMonoidHom) ρCore) {g : Γ} (hg3 : g ^ 3 = 1) (hg1 : g ≠ 1) :
    16 * Nat.card (Fix ρ {g}) ≤ Nat.card M := by
  obtain ⟨f, hf, hfe⟩ := h
  have hfe' : ∀ g c, f ((ρCore.comp graph.toMonoidHom) g c) = ρ g (f c) := by
    intro g c
    have := hfe (graph g) c
    rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, graph_graph] at this
    exact this
  have hfix1 : Nat.card (Fix (ρCore.comp graph.toMonoidHom) {g}) =
      Nat.card (Fix ρCore {graph g}) :=
    Nat.card_congr (Equiv.subtypeEquivRight fun c => by
      simp only [Set.mem_singleton_iff, forall_eq]
      exact Iff.rfl)
  rw [card_fix_of_iso f hf hfe', hfix1, card_fix_core_one,
    ← Nat.card_congr (Equiv.ofBijective f hf), card_core]
  have := core_fix_three (graph g) (by rw [← map_pow, hg3, map_one])
    (fun h1 => hg1 (graph.injective (by rw [h1, map_one])))
  omega

theorem fix_three_sum {ρ : Γ →* AddMonoid.End M} (h : IsoMod ρ ρSum) {g : Γ} (hg3 : g ^ 3 = 1)
    (hg1 : g ≠ 1) : 16 * Nat.card (Fix ρ {g}) ≤ Nat.card M := by
  obtain ⟨f, hf, hfe⟩ := h
  have h1 : Nat.card (Fix ρ {g}) = (Finset.univ.filter fun p : V3 × V3 =>
      g • p.1 = p.1 ∧ graph g • p.2 = p.2).card :=
    (card_fix_of_iso f hf hfe {g}).trans (card_fix_sum_one g)
  have h2 : Nat.card M = 64 := (Nat.card_congr (Equiv.ofBijective f hf)).symm.trans card_sum
  rw [h1, h2]
  have := sum_fix_three g hg3 hg1
  omega

end L32Mod

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

theorem s1347_module_fix3 (S : A6.Setting134 G T L V) {H₁ H₂ : Subgroup G}
    (hH₀ : InH T (H₁ ⊔ H₂)) {ψ : ↥(H₁ ⊔ H₂) →* SL3.S}
    (hTψ : (T.subgroupOf (H₁ ⊔ H₂)).map ψ = SL3.P0)
    {σ : SL3.S →* MulAut ↥(v0Of T H₁ H₂)}
    (hσ : ∀ (k : ↥(H₁ ⊔ H₂)) (w : ↥(v0Of T H₁ H₂)),
      ((σ (ψ k) w : ↥(v0Of T H₁ H₂)) : G) = k * w * (k : G)⁻¹)
    {Hp Hl : Subgroup G} (hHp : Hp ≤ H₁ ⊔ H₂) (hHl : Hl ≤ H₁ ⊔ H₂)
    (hpX : (Hp.subgroupOf (H₁ ⊔ H₂)).map ψ = SL3.X1)
    (hlX : (Hl.subgroupOf (H₁ ⊔ H₂)).map ψ = SL3.X2) {x y : ↥(v0Of T H₁ H₂)}
    (hxp : (x : G) ∈ centralizer (Hp : Set G)) (hyl : (y : G) ∈ centralizer (Hl : Set G))
    (hxl : (x : G) ∉ centralizer (Hl : Set G)) (hyp : (y : G) ∉ centralizer (Hp : Set G))
    (hZ : ∀ z ∈ quasithinOmegaOneCenter T, z = 1 ∨ z = x ∨ z = y ∨ z = (x : G) * y)
    {g : SL3.S} (hg3 : g ^ 3 = 1) (hg1 : g ≠ 1) :
    ∃ _ : IsMulCommutative ↥(v0Of T H₁ H₂),
      16 * Nat.card (L32Mod.Fix (L32Mod.toAddRep σ) {g}) ≤
        Nat.card (Additive ↥(v0Of T H₁ H₂)) := by
  have hred := s1347_reduced S hH₀
  have hcomm : IsMulCommutative ↥(v0Of T H₁ H₂) := hred.2.2.1.1
  refine ⟨hcomm, ?_⟩
  have h2 : ∀ m : Additive ↥(v0Of T H₁ H₂), m + m = 0 := by
    intro m
    have : Additive.toMul m * Additive.toMul m = 1 :=
      Subtype.ext (by rw [Subgroup.coe_mul, ← pow_two]; exact hred.2.2.1.2 _ (Additive.toMul m).2)
    exact congrArg Additive.ofMul this
  obtain ⟨hx, hy, hxl', hyp'⟩ := s1347_l32_hyps hσ hpX hlX hHl hHp hxp hyl hxl hyp
  have hgen := s1347_l32_gen hσ hZ
  have hC := s1347_l32_fixed S hH₀ hTψ hσ hZ
  rcases L32Mod.l32_cases h2 hx hy hxl' hyp' hgen hC with hiso | hiso |
    ⟨U₁, U₂, hsup, hinf, hinv₁, hinv₂, ⟨e₁, he₁⟩, ⟨e₂, he₂⟩⟩
  · exact L32Mod.fix_three_core hiso hg3 hg1
  · exact L32Mod.fix_three_core_graph hiso hg3 hg1
  · exact L32Mod.fix_three_sum (L32Mod.isoMod_sum hsup hinf e₁ he₁ hinv₁ hinv₂ e₂ he₂) hg3 hg1

theorem s1347_L32_relIndex (hedge : GoldschmidtEdgeBoundS3) (h1332 : Stmt13_3_2)
    (h1228 : Stmt12_2_8) (hC58 : TheoremC58) (h317 : AS317Sylow) (h56 : AsB56)
    (h135 : A6.Stmt13_3_5) (S : A6.Setting134 G T L V) {H₁ H₂ : Subgroup G}
    (h : Hyp1347 T H₁ H₂) {K₀ : Subgroup G}
    (hN : H₁ ⊔ H₂ ≤ normalizer (K₀ : Set G))
    (hK : quasithinO2QuotientIso K₀ SL3.S) (hsup : H₁ ⊔ H₂ = K₀ ⊔ T)
    {c : G} (hcH : c ∈ H₁ ⊔ H₂) (hc3 : c ^ 3 = 1)
    (hcC : c ∉ centralizer (v0Of T H₁ H₂ : Set G)) :
    16 ≤ (centralizer ({c} : Set G)).relIndex (v0Of T H₁ H₂) := by
  obtain ⟨hH₀, -, -, hZsup, hZinf, hc₁, hc₂⟩ :=
    s1347_one_first hedge h1332 h1228 hC58 h317 h56 h135 S h
  have hiso₀ := s1347_quotIso_H0 S h hN hK hsup
  have hsyl₀ : IsSylowTwoOf T (H₁ ⊔ H₂) := A5.isSylowTwoOf_of_le S.h13.sylow hH₀.1
  obtain ⟨ψ, hψ, hker, hTψ⟩ := I51.exists_model_hom hiso₀ hsyl₀ SL3.P0_sylow.1 SL3.P0_sylow.2
  have hcent := s1347_centralizer_eq S h hH₀ hiso₀
  obtain ⟨σ, hσ⟩ := s1347_exists_action S h hH₀ hψ hker
  have h3₁ := s1347_relIndex_three S h.inH₁.1 h.s3₁
  have h3₂ := s1347_relIndex_three S h.inH₂.1 h.s3₂
  have hP₁ := s1347_map_parabolic hsyl₀ hker hTψ le_sup_left h.inH₁.1 h3₁
  have hP₂ := s1347_map_parabolic hsyl₀ hker hTψ le_sup_right h.inH₂.1 h3₂
  have hne := s1347_map_ne hsyl₀ hker le_sup_left le_sup_right h.inH₁.1 h.inH₂.1 h.ne
  obtain ⟨u, hu, hu1⟩ := exists_ne_one_of_card_two hc₁
  obtain ⟨v, hv, hv1⟩ := exists_ne_one_of_card_two hc₂
  have hZ := s1347_Z_eq hZsup hc₁ hc₂ hu hu1 hv hv1
  have huZ : u ∈ quasithinOmegaOneCenter T := (mem_inf.1 hu).1
  have hvZ : v ∈ quasithinOmegaOneCenter T := (mem_inf.1 hv).1
  have hu₂ : u ∉ centralizer (H₂ : Set G) := fun h' => hu1 (by
    have : u ∈ cZ T H₁ ⊓ cZ T H₂ := mem_inf.2 ⟨hu, mem_inf.2 ⟨huZ, h'⟩⟩
    rwa [hZinf, mem_bot] at this)
  have hv₁ : v ∉ centralizer (H₁ : Set G) := fun h' => hv1 (by
    have : v ∈ cZ T H₁ ⊓ cZ T H₂ := mem_inf.2 ⟨mem_inf.2 ⟨hvZ, h'⟩, hv⟩
    rwa [hZinf, mem_bot] at this)
  set uV : ↥(v0Of T H₁ H₂) := ⟨u, s1347_Z_le_V0 huZ⟩
  set vV : ↥(v0Of T H₁ H₂) := ⟨v, s1347_Z_le_V0 hvZ⟩
  set c' : ↥(H₁ ⊔ H₂) := ⟨c, hcH⟩ with hc'
  have hg3 : ψ c' ^ 3 = 1 := by
    have : c' ^ 3 = 1 := Subtype.ext (by simpa [hc'] using hc3)
    rw [← map_pow, this, map_one]
  have hg1 : ψ c' ≠ 1 := by
    intro h1
    have := (map_eq_one_iff_of_ker hker _).1 h1
    rw [← hcent] at this
    exact hcC this.2
  have hfix : ∃ _ : IsMulCommutative ↥(v0Of T H₁ H₂),
      16 * Nat.card (L32Mod.Fix (L32Mod.toAddRep σ) {ψ c'}) ≤
        Nat.card (Additive ↥(v0Of T H₁ H₂)) := by
    rcases hP₂ with h2X | h2X
    · have h1X : (H₁.subgroupOf (H₁ ⊔ H₂)).map ψ = SL3.X2 :=
        hP₁.resolve_left fun h1X => hne (h1X.trans h2X.symm)
      refine s1347_module_fix3 S hH₀ hTψ hσ le_sup_right le_sup_left h2X h1X
        (x := vV) (y := uV) (mem_inf.1 hv).2 (mem_inf.1 hu).2 hv₁ hu₂ (fun z hz => ?_) hg3 hg1
      rcases hZ z hz with h' | h' | h' | h'
      · exact Or.inl h'
      · exact Or.inr (Or.inr (Or.inl h'))
      · exact Or.inr (Or.inl h')
      · exact Or.inr (Or.inr (Or.inr (h'.trans (s1347_Z_comm huZ hvZ))))
    · have h1X : (H₁.subgroupOf (H₁ ⊔ H₂)).map ψ = SL3.X1 :=
        hP₁.resolve_right fun h1X => hne (h1X.trans h2X.symm)
      exact s1347_module_fix3 S hH₀ hTψ hσ le_sup_left le_sup_right h1X h2X
        (x := uV) (y := vV) (mem_inf.1 hu).2 (mem_inf.1 hv).2 hu₂ hv₁ hZ hg3 hg1
  obtain ⟨hcomm, hfix⟩ := hfix
  have hcardF : Nat.card (L32Mod.Fix (L32Mod.toAddRep σ) {ψ c'}) =
      Nat.card ↥(centralizer ({c} : Set G) ⊓ v0Of T H₁ H₂) := by
    refine Nat.card_congr
      { toFun := fun m => ⟨((Additive.toMul m.1 : ↥(v0Of T H₁ H₂)) : G),
          mem_inf.2 ⟨mem_centralizer_singleton_iff.2 ?_, (Additive.toMul m.1).2⟩⟩
        invFun := fun w => ⟨Additive.ofMul ⟨w, (mem_inf.1 w.2).2⟩, ?_⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    · have := m.2 (ψ c') rfl
      exact ((s1347_fix_iff hσ c' (Additive.toMul m.1)).1 this).symm
    · rintro _ rfl
      exact (s1347_fix_iff hσ c' _).2 (mem_centralizer_singleton_iff.1 (mem_inf.1 w.2).1).symm
  have hcardV : Nat.card (Additive ↥(v0Of T H₁ H₂)) = Nat.card ↥(v0Of T H₁ H₂) := rfl
  rw [hcardF, hcardV] at hfix
  have hrel := relIndex_mul_card (centralizer ({c} : Set G)) (v0Of T H₁ H₂)
  have hpos : 0 < Nat.card ↥(centralizer ({c} : Set G) ⊓ v0Of T H₁ H₂) := Nat.card_pos
  by_contra hlt
  push Not at hlt
  have : (centralizer ({c} : Set G)).relIndex (v0Of T H₁ H₂) *
      Nat.card ↥(centralizer ({c} : Set G) ⊓ v0Of T H₁ H₂) <
        16 * Nat.card ↥(centralizer ({c} : Set G) ⊓ v0Of T H₁ H₂) :=
    Nat.mul_lt_mul_of_pos_right hlt hpos
  omega

theorem s1347_A6_relIndex (hedge : GoldschmidtEdgeBoundS3) (h1332 : Stmt13_3_2)
    (h1228 : Stmt12_2_8) (hC58 : TheoremC58) (h317 : AS317Sylow) (h56 : AsB56)
    (h135 : A6.Stmt13_3_5) (h1345 : NQS134.Stmt13_4_5) (S : A6.Setting134 G T L V)
    {H₁ H₂ : Subgroup G} (h : Hyp1347 T H₁ H₂) (hns : ¬ Group.IsSolvable ↥(H₁ ⊔ H₂))
    {K₀ : Subgroup G} (hK₀ : K₀ ∈ cComp (H₁ ⊔ H₂)) (hN : H₁ ⊔ H₂ ≤ normalizer (K₀ : Set G))
    (hA6 : Nonempty (↥K₀ ⧸ CFSG.pCore 2 ↥K₀ ≃* alternatingGroup (Fin 6)))
    (hK₁ : oTwoRes H₁ ≤ K₀) (hK₂ : oTwoRes H₂ ≤ K₀) (hsup : H₁ ⊔ H₂ = K₀ ⊔ T)
    (hcentK : K₀ ⊓ centralizer (v0Of T H₁ H₂ : Set G) = pCoreOf 2 K₀) {c : G} (hcK : c ∈ K₀)
    (hc3 : c ^ 3 = 1) (hcC : c ∉ centralizer (v0Of T H₁ H₂ : Set G)) :
    16 ≤ (centralizer ({c} : Set G)).relIndex (v0Of T H₁ H₂) := by
  obtain ⟨I, hIc, hH₀I, ρ, ψ, F₀, hIV, hψ, -, hρK, hkerV, hF₀s, hF₀I, hF₀⟩ :=
    s1347_A6_data hedge h1332 h1228 hC58 h317 h56 h135 h1345 S h hns hK₀ hN hA6 hK₁ hK₂ hsup
      hcentK
  have hKH := le_of_mem_cComp hK₀
  set c' : ↥(H₁ ⊔ H₂) := ⟨c, hKH hcK⟩ with hc'
  set s := ρ c' with hs
  have hsA : s ∈ alternatingGroup (Fin 6) := hρK c' hcK
  have hs3 : s ^ 3 = 1 := by
    have : c' ^ 3 = 1 := Subtype.ext (by simpa [hc'] using hc3)
    rw [hs, ← map_pow, this, map_one]
  have hs1 : s ≠ 1 := fun h1 => hcC ((hkerV c').1 h1)
  have hI16 : Nat.card I = 16 := by
    rw [Nat.card_congr ψ.toEquiv]
    have h1 : Fintype.card {x : P6 // InW4 x} = 16 := by decide +kernel
    rw [← h1, ← Nat.card_eq_fintype_card]
    rfl
  have hch := chain_ineq hIV F₀ hF₀s hF₀I hI16 (C := centralizer ({c} : Set G))
    (fun w => ∀ a ∈ ({S6Out.phiEquiv.symm s} : Set (Perm (Fin 6))), act4 a w = w)
    (fun x hx => by
      rintro a rfl
      have hcx : c * (x : G) * c⁻¹ = x := by
        rw [← mem_centralizer_singleton_iff.1 hx, mul_inv_cancel_right]
      have h1 := hF₀ c' x (by rw [show (c' : G) = c from rfl, hcx]; exact x.2) (Or.inr hcK)
      have e : (⟨(c' : G) * x * (c' : G)⁻¹, by rw [show (c' : G) = c from rfl, hcx]; exact x.2⟩ :
          ↥(v0Of T H₁ H₂)) = x := Subtype.ext hcx
      rw [e] at h1
      exact h1.symm)
  have hfI : Nat.card ↥(I ⊓ centralizer ({c} : Set G)) ≤
      Nat.card {x : ↥W4 // ∀ a ∈ ({s} : Set (Perm (Fin 6))), act4 a x = x} := by
    refine Nat.card_le_card_of_injective (fun v => ⟨ψ ⟨v, (mem_inf.1 v.2).1⟩, ?_⟩) ?_
    · rintro a rfl
      rw [hs, ← hψ]
      congr 1
      apply Subtype.ext
      rw [conjAct_val]
      show c * (v : G) * c⁻¹ = v
      rw [← mem_centralizer_singleton_iff.1 (mem_inf.1 v.2).2, mul_inv_cancel_right]
    · intro v w hvw
      have h1 := ψ.injective (congrArg Subtype.val hvw)
      exact Subtype.ext (congrArg (fun z : ↥I => (z : G)) h1)
  have hf1 := S6Out.card_fix_le (S := ({s} : Set (Perm (Fin 6)))) (L := [s]) (by simp)
  have hf2 : Nat.card {w : ↥W4 //
      ∀ a ∈ ({S6Out.phiEquiv.symm s} : Set (Perm (Fin 6))), act4 a w = w} ≤
        S6Out.fixCount [S6Out.phi (S6Out.cc⁻¹ * s * S6Out.cc)] :=
    S6Out.card_fix_le fun x hx => by
      rw [List.mem_singleton] at hx
      rw [hx, ← S6Out.phi_inv_eq]
      exact Set.mem_singleton _
  have hprod := a6_fix_three s hs3 hs1 (Perm.mem_alternatingGroup.1 hsA)
  have hkey : 256 * Nat.card ↥(v0Of T H₁ H₂ ⊓ centralizer ({c} : Set G)) ≤
      4 * Nat.card ↥(v0Of T H₁ H₂) := by
    calc 256 * Nat.card ↥(v0Of T H₁ H₂ ⊓ centralizer ({c} : Set G)) ≤
          Nat.card ↥(v0Of T H₁ H₂) * Nat.card ↥(I ⊓ centralizer ({c} : Set G)) *
            Nat.card {w : ↥W4 //
              ∀ a ∈ ({S6Out.phiEquiv.symm s} : Set (Perm (Fin 6))), act4 a w = w} := hch
      _ ≤ Nat.card ↥(v0Of T H₁ H₂) * (S6Out.fixCount [s] *
            S6Out.fixCount [S6Out.phi (S6Out.cc⁻¹ * s * S6Out.cc)]) := by
        rw [mul_assoc]
        exact Nat.mul_le_mul_left _ (Nat.mul_le_mul (hfI.trans hf1) hf2)
      _ ≤ Nat.card ↥(v0Of T H₁ H₂) * 4 := Nat.mul_le_mul_left _ hprod
      _ = 4 * Nat.card ↥(v0Of T H₁ H₂) := mul_comm _ _
  have hrel := relIndex_mul_card (centralizer ({c} : Set G)) (v0Of T H₁ H₂)
  rw [inf_comm] at hrel
  have hpos : 0 < Nat.card ↥(v0Of T H₁ H₂ ⊓ centralizer ({c} : Set G)) := Nat.card_pos
  by_contra hlt
  push Not at hlt
  have : (centralizer ({c} : Set G)).relIndex (v0Of T H₁ H₂) *
      Nat.card ↥(v0Of T H₁ H₂ ⊓ centralizer ({c} : Set G)) <
        16 * Nat.card ↥(v0Of T H₁ H₂ ⊓ centralizer ({c} : Set G)) :=
    Nat.mul_lt_mul_of_pos_right hlt hpos
  omega

end CFSG.Quasithin.H13.U3
