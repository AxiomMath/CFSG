module

public import CFSG.Quasithin.H13.U3S13472E

public section

namespace CFSG.Quasithin.H13.U3

open Subgroup Equiv CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.H13.A6 CFSG.LieType.BorelTits
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

namespace P2

variable {S : A6.Setting134 G T L V} {H₁ H₂ : Subgroup G}

@[expose] def IsTwoCent (K : Subgroup G) (z : G) : Prop :=
  ∀ k ∈ K, k * z = z * k → ∃ n : ℕ, k ^ 2 ^ n = 1

omit [Finite G] in
theorem isTwoCent_of_conj {K : Subgroup G} {g : G} (hg : g ∈ normalizer (K : Set G)) {z : G}
    (h : IsTwoCent K (g * z * g⁻¹)) : IsTwoCent K z := by
  intro k hk hkz
  have hk' : g * k * g⁻¹ ∈ K := (mem_normalizer_iff.1 hg k).1 hk
  have hc : (g * k * g⁻¹) * (g * z * g⁻¹) = (g * z * g⁻¹) * (g * k * g⁻¹) := by
    calc (g * k * g⁻¹) * (g * z * g⁻¹) = g * (k * z) * g⁻¹ := by group
      _ = g * (z * k) * g⁻¹ := by rw [hkz]
      _ = (g * z * g⁻¹) * (g * k * g⁻¹) := by group
  obtain ⟨n, hn⟩ := h _ hk' hc
  refine ⟨n, ?_⟩
  rw [conj_pow] at hn
  have := congrArg (fun x => g⁻¹ * x * g) hn
  simpa [mul_assoc] using this

omit [Finite G] in
theorem isTwoCent_conj_iff {K : Subgroup G} {g : G} (hg : g ∈ normalizer (K : Set G)) (z : G) :
    IsTwoCent K (g * z * g⁻¹) ↔ IsTwoCent K z := by
  refine ⟨isTwoCent_of_conj hg, fun h => isTwoCent_of_conj (g := g⁻¹) (inv_mem hg) ?_⟩
  rwa [show g⁻¹ * (g * z * g⁻¹) * g⁻¹⁻¹ = z by group]

theorem mem_normalizer_of_conj_le {H : Subgroup G} {y : G} (h : ∀ x ∈ H, y * x * y⁻¹ ∈ H) :
    y ∈ normalizer (H : Set G) := by
  have hle : H.map (MulAut.conj y).toMonoidHom ≤ H := by
    rintro _ ⟨x, hx, rfl⟩
    exact h x hx
  have heq : H.map (MulAut.conj y).toMonoidHom = H :=
    Subgroup.eq_of_le_of_card_ge hle (by
      rw [Subgroup.card_map_of_injective (MulAut.conj y).injective])
  refine mem_normalizer_iff.mpr fun x => ⟨h x, fun hx => ?_⟩
  rw [← heq] at hx
  obtain ⟨x', hx', hxx⟩ := hx
  have : x' = x := by
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hxx
    have := congrArg (fun z => y⁻¹ * z * y) hxx
    simpa [mul_assoc] using this
  rwa [← this]

theorem isSylowTwoOf_conj {P K : Subgroup G} (hP : IsSylowTwoOf P K) {g : G}
    (hg : g ∈ normalizer (K : Set G)) : IsSylowTwoOf (P.map (MulAut.conj g).toMonoidHom) K := by
  have hKmap : K.map (MulAut.conj g).toMonoidHom = K := by
    refine Subgroup.eq_of_le_of_card_ge ?_
      (by rw [Subgroup.card_map_of_injective (MulAut.conj g).injective])
    rintro _ ⟨x, hx, rfl⟩
    exact (mem_normalizer_iff.1 hg x).1 hx
  refine ⟨?_, hP.2.1.map _, ?_⟩
  · rw [← hKmap]
    exact map_mono hP.1
  · have h1 := Subgroup.relIndex_map_map_of_injective P K
      (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective
    rw [← hKmap]
    show ¬ 2 ∣ Subgroup.relIndex _ _
    rw [h1]
    exact hP.2.2

theorem normalizer_Z_le (D : Data2 S H₁ H₂) {X : Subgroup G} (hS : SettingX D X) :
    X ⊓ normalizer (quasithinOmegaOneCenter T : Set G) ≤ T := by
  have hx1 : (D.x : G) ≠ 1 := fun h => D.hxnl (h ▸ one_mem _)
  have hcommZ : (D.x : G) * D.y = D.y * D.x := s1347_Z_comm D.hxZ D.hyZ
  have hPxy : IsTwoCent D.K₀ ((D.x : G) * D.y) := fun k hk hc => D.isTwo_of_comm_xy hk hc
  have hnot : ∀ {z : G}, (∃ k ∈ D.K₀, k * z = z * k ∧ ∀ n : ℕ, k ^ 2 ^ n ≠ 1) →
      ¬ IsTwoCent D.K₀ z := by
    rintro z ⟨k, hk, hkz, hn⟩ h
    obtain ⟨n, hn'⟩ := h k hk hkz
    exact hn n hn'
  have hPx : ¬ IsTwoCent D.K₀ (D.x : G) := hnot D.exists_comm_x
  have hPy : ¬ IsTwoCent D.K₀ (D.y : G) := hnot D.exists_comm_y
  have hP1 : ¬ IsTwoCent D.K₀ 1 := by
    obtain ⟨k, hk, -, hn⟩ := D.exists_comm_x
    exact hnot ⟨k, hk, by rw [mul_one, one_mul], hn⟩
  have hsq : ∀ g ∈ X, g ∈ normalizer (quasithinOmegaOneCenter T : Set G) → g * g ∈ T := by
    intro g hgX hgN
    have hgK := hS.hNX hgX
    have hZg : ∀ z ∈ quasithinOmegaOneCenter T, g * z * g⁻¹ ∈ quasithinOmegaOneCenter T :=
      fun z hz => (mem_normalizer_iff.1 hgN z).1 hz
    have hxy : g * ((D.x : G) * D.y) * g⁻¹ = (D.x : G) * D.y := by
      have hP := (isTwoCent_conj_iff hgK _).2 hPxy
      rcases D.hZ _ (hZg _ (mul_mem D.hxZ D.hyZ)) with h | h | h | h
      · exact absurd (h ▸ hP) hP1
      · exact absurd (h ▸ hP) hPx
      · exact absurd (h ▸ hP) hPy
      · exact h
    have hgx : g * D.x * g⁻¹ = D.x ∨ g * D.x * g⁻¹ = D.y := by
      have hP : ¬ IsTwoCent D.K₀ (g * D.x * g⁻¹) := fun h =>
        hPx ((isTwoCent_conj_iff hgK _).1 h)
      rcases D.hZ _ (hZg _ D.hxZ) with h | h | h | h
      · exfalso
        apply hx1
        have := congrArg (fun z => g⁻¹ * z * g) h
        simpa [mul_assoc] using this
      · exact Or.inl h
      · exact Or.inr h
      · exact absurd (h ▸ hPxy) hP
    have hgy : g * D.y * g⁻¹ = (g * D.x * g⁻¹)⁻¹ * ((D.x : G) * D.y) := by
      rw [← hxy]
      group
    have hcent : ∀ c : G, c * D.x * c⁻¹ = D.x → c * D.y * c⁻¹ = D.y → c ∈ X →
        c ∈ T := by
      intro c hcx hcy hcX
      rw [← hS.hXZ]
      refine ⟨hcX, mem_centralizer_iff.2 fun z hz => ?_⟩
      have hfix : c * z * c⁻¹ = z := by
        rcases D.hZ z hz with rfl | rfl | rfl | rfl
        · group
        · exact hcx
        · exact hcy
        · rw [show c * ((D.x : G) * D.y) * c⁻¹ = (c * D.x * c⁻¹) * (c * D.y * c⁻¹) by group,
            hcx, hcy]
      calc z * c = (c * z * c⁻¹) * c := by rw [hfix]
        _ = c * z := by group
    rcases hgx with h | h
    · have hgy' : g * D.y * g⁻¹ = D.y := by
        rw [hgy, h, ← mul_assoc, inv_mul_cancel, one_mul]
      exact mul_mem (hcent g h hgy' hgX) (hcent g h hgy' hgX)
    · have hgy' : g * D.y * g⁻¹ = D.x := by
        rw [hgy, h, hcommZ, ← mul_assoc, inv_mul_cancel, one_mul]
      refine hcent (g * g) ?_ ?_ (mul_mem hgX hgX)
      · rw [show g * g * D.x * (g * g)⁻¹ = g * (g * D.x * g⁻¹) * g⁻¹ by group, h, hgy']
      · rw [show g * g * D.y * (g * g)⁻¹ = g * (g * D.y * g⁻¹) * g⁻¹ by group, hgy', h]
  have hP : IsPGroup 2 ↥(X ⊓ normalizer (quasithinOmegaOneCenter T : Set G)) := by
    rintro ⟨g, hgX, hgN⟩
    obtain ⟨n, hn⟩ := S.h13.sylow.1 ⟨g * g, hsq g hgX hgN⟩
    refine ⟨n + 1, Subtype.ext ?_⟩
    have h1 : (g * g) ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
    rw [pow_succ', pow_mul, sq, h1]
  have hTN : T ≤ normalizer (quasithinOmegaOneCenter T : Set G) := fun t ht =>
    mem_normalizer_of_conj_le fun z hz => by
      rw [show t * z * t⁻¹ = z by
        rw [mem_centralizer_iff.1 (s134_Z_le_center T hz).2 t ht, mul_inv_cancel_right]]
      exact hz
  exact (A4.isSylowTwoOf_iff_maximal.1 hS.sylow).2.2 _ inf_le_left hP (le_inf hS.TX hTN)

theorem eq_H0_of (D : Data2 S H₁ H₂) {X : Subgroup G} (hS : SettingX D X)
    (hW : conjClosure (quasithinOmegaOneCenter T) X = v0Of T H₁ H₂) : X = H₁ ⊔ H₂ := by
  refine le_antisymm (fun g hg => ?_) hS.hX.1
  rw [D.hsup]
  have hXV : X ≤ normalizer (v0Of T H₁ H₂ : Set G) := hW ▸ hS.reduced.2.1
  have hgK : g ∈ normalizer (D.K₀ : Set G) := hS.hNX hg
  have hsyl : IsSylowTwoOf (T ⊓ D.K₀) D.K₀ := A4.isSylowTwoOf_inf_normal hS.sylow hS.KX hS.hNX
  obtain ⟨k, hk, hkS⟩ := A4.exists_conj_of_isSylowTwoOf hsyl (isSylowTwoOf_conj hsyl hgK)
  have hconj : ∀ s ∈ T ⊓ D.K₀, (k⁻¹ * g)⁻¹ * s * (k⁻¹ * g) ∈ T ⊓ D.K₀ := by
    intro s hs
    have h1 : k * s * k⁻¹ ∈ (T ⊓ D.K₀).map (MulAut.conj g).toMonoidHom :=
      (hkS _).2 (by simpa [mul_assoc] using hs)
    obtain ⟨s', hs', hs's⟩ := h1
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hs's
    have e : (k⁻¹ * g)⁻¹ * s * (k⁻¹ * g) = s' := by
      calc (k⁻¹ * g)⁻¹ * s * (k⁻¹ * g) = g⁻¹ * (k * s * k⁻¹) * g := by group
        _ = g⁻¹ * (g * s' * g⁻¹) * g := by rw [hs's]
        _ = s' := by group
    rw [e]
    exact hs'
  have hhX : k⁻¹ * g ∈ X := mul_mem (inv_mem (hS.KX hk)) hg
  have hhZ : ∀ z ∈ quasithinOmegaOneCenter T,
      (k⁻¹ * g) * z * (k⁻¹ * g)⁻¹ ∈ quasithinOmegaOneCenter T := by
    intro z hz
    have hzV : (k⁻¹ * g) * z * (k⁻¹ * g)⁻¹ ∈ v0Of T H₁ H₂ :=
      (mem_normalizer_iff.1 (hXV hhX) z).1 (s1347_Z_le_V0 hz)
    refine D.mem_Z_of_fixed hzV fun s hs => ?_
    have hs' := hconj s hs
    have hc : ((k⁻¹ * g)⁻¹ * s * (k⁻¹ * g)) * z = z * ((k⁻¹ * g)⁻¹ * s * (k⁻¹ * g)) :=
      mem_centralizer_iff.1 (s134_Z_le_center T hz).2 _ hs'.1
    calc s * ((k⁻¹ * g) * z * (k⁻¹ * g)⁻¹) =
        (k⁻¹ * g) * (((k⁻¹ * g)⁻¹ * s * (k⁻¹ * g)) * z) * (k⁻¹ * g)⁻¹ := by group
      _ = (k⁻¹ * g) * (z * ((k⁻¹ * g)⁻¹ * s * (k⁻¹ * g))) * (k⁻¹ * g)⁻¹ := by rw [hc]
      _ = (k⁻¹ * g) * z * (k⁻¹ * g)⁻¹ * s := by group
  have hhT : k⁻¹ * g ∈ T :=
    normalizer_Z_le D hS ⟨hhX, mem_normalizer_of_conj_le hhZ⟩
  have e : g = k * (k⁻¹ * g) := by group
  rw [e]
  exact mul_mem (mem_sup_left hk) (mem_sup_right hhT)

end P2

theorem s1347_two (hC137 : C137StatementFiveZ)
    (hedge : GoldschmidtEdgeBoundS3) (h1332 : Stmt13_3_2) (h1228 : Stmt12_2_8)
    (hC58 : TheoremC58) (h317 : AS317Sylow) (h56 : AsB56) (h135 : A6.Stmt13_3_5)
    (h1345 : NQS134.Stmt13_4_5) (hF : F6.TheoremF618Cat) (hBig : A5.FactF618Big)
    (h37 : Vol2Native.A37ForSQTKCat) (h39 : Vol2Native.A39ForSQTKCat)
    (S : A6.Setting134 G T L V) {H₁ H₂ : Subgroup G} (h : Hyp1347 T H₁ H₂)
    (hK₂L : oTwoRes H₂ = l2Of S) (hii : Concl1347ii T H₁ H₂) {X : Subgroup G}
    (hX : InH (H₁ ⊔ H₂) X)
    (hXZ : X ⊓ centralizer (quasithinOmegaOneCenter T : Set G) = T) : X = H₁ ⊔ H₂ := by
  have hJ1 :=
    (s1347_four hC137 hedge h1332 h1228 hC58 h317 h56 h135 h1345 hF hBig S h hK₂L).2 hii
  obtain ⟨D⟩ := P2.exists_data2 hedge h1332 h1228 hC58 h317 h56 h135 h1345 S h hii
  have hS := P2.settingX_of h37 h39 h1345 D hX hXZ
  obtain ⟨A, hA, hAC⟩ := P2.exists_A D hJ1
  by_cases hB : (A ⊓ centralizer (v0Of T H₁ H₂ : Set G)) ⊔ v0Of T H₁ H₂ ≤
      centralizer (conjClosure (quasithinOmegaOneCenter T) X : Set G)
  · exact P2.eq_H0_of D hS (P2.eq_V0_of_B D hS hA hAC hB)
  · exact (P2.false_of_not_B h56 D hS hA hAC hB).elim

theorem s1347_two_forall (hC137 : C137StatementFiveZ)
    (hedge : GoldschmidtEdgeBoundS3) (h1332 : Stmt13_3_2) (h1228 : Stmt12_2_8)
    (hC58 : TheoremC58) (h317 : AS317Sylow) (h56 : AsB56) (h135 : A6.Stmt13_3_5)
    (h1345 : NQS134.Stmt13_4_5) (hF : F6.TheoremF618Cat) (hBig : A5.FactF618Big)
    (h37 : Vol2Native.A37ForSQTKCat) (h39 : Vol2Native.A39ForSQTKCat) :
    ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G)
      (S : A6.Setting134 G T L V) (H₁ H₂ : Subgroup G), Hyp1347 T H₁ H₂ →
      oTwoRes H₂ = l2Of S → Concl1347ii T H₁ H₂ → ∀ X : Subgroup G, InH (H₁ ⊔ H₂) X →
        X ⊓ centralizer (quasithinOmegaOneCenter T : Set G) = T → X = H₁ ⊔ H₂ :=
  fun _ _ _ _ _ _ S _ _ h hK₂L hii _ hX hXZ =>
    s1347_two hC137 hedge h1332 h1228 hC58 h317 h56 h135 h1345 hF hBig h37 h39 S h hK₂L hii hX
      hXZ

end CFSG.Quasithin.H13.U3
