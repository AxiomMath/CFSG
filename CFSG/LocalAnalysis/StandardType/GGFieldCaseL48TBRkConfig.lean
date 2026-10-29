module

public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL48TBRkDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem coverP_at_of_tableBRk {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J X B₂ : Subgroup G} {d y : G} {K U U₁ : Subgroup G}
    (hS : GGFieldCaseSetup p B Bs x L D J X B₂ d y K U U₁)
    (hN : Subgroup.centralizer ({x} : Set G) ≤ Subgroup.normalizer (L : Set G))
    {R : Type} [Group R] {I : Set (MulAut R)} (θ : L ⧸ Subgroup.center L ≃* R)
    (hL : commutator L = ⊤) (hBsN : Bs ≤ Subgroup.normalizer (L : Set G))
    (h3 : ∀ b ∈ Bs, ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ)
    {r : ℕ} (hKG : GGCoverPTableBRk p R I r) (hr : p ^ r ≤ Nat.card Bs) :
    ∀ h ∈ Subgroup.centralizer ({x} : Set G), (∃ k : ℕ, h ^ p ^ k = 1) →
      h ∈ (Subgroup.centralizer ({x} : Set G) ⊓
          Subgroup.centralizer ((Bs ⊓ Subgroup.centralizer (X : Set G) : Subgroup G) : Set G)) ⊔
        L ⊔ (Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer (L : Set G)) := by
  intro h hh ⟨k, hk⟩
  have hLx : L ≤ Subgroup.centralizer ({x} : Set G) := hS.1.1.1.2.2.2.2.2.2.1.2.2.2.1.1
  set hN' : Subgroup.normalizer (L : Set G) := ⟨h, hN hh⟩ with hhN
  have ha : ggLAut L θ hN' ^ p ^ k = 1 := by
    rw [← map_pow]
    have : hN' ^ p ^ k = 1 := Subtype.ext (by simpa [hhN] using hk)
    rw [this, map_one]
  obtain ⟨ρ, hρ⟩ := hKG G L Bs θ hBsN (tableBPosition_of_setup hS θ hL hBsN h3) hr _ ⟨k, ha⟩
  obtain ⟨q, rfl⟩ := θ.surjective ρ
  obtain ⟨ℓ, rfl⟩ := QuotientGroup.mk_surjective q
  have hℓH : (ℓ : G) ∈ Subgroup.centralizer ({x} : Set G) := hLx ℓ.2
  set g := (ℓ : G)⁻¹ * h with hg
  have hgH : g ∈ Subgroup.centralizer ({x} : Set G) :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ hℓH) hh
  set gN : Subgroup.normalizer (L : Set G) := ⟨g, hN hgH⟩ with hgN
  have hgA : ggLAut L θ gN =
      (MulAut.conj (θ (QuotientGroup.mk ℓ)))⁻¹ * ggLAut L θ hN' := by
    rw [← ggLAut_of_mem_conj θ ℓ (hN hℓH), ← map_inv, ← map_mul]
    congr 1
  have hcomm : ∀ b ∈ Bs ⊓ Subgroup.centralizer (X : Set G),
      g * b * g⁻¹ * b⁻¹ ∈ Subgroup.centralizer (L : Set G) := by
    intro b hb
    set bN : Subgroup.normalizer (L : Set G) := ⟨b, hBsN hb.1⟩ with hbN
    have h1 : ggLAut L θ (gN * bN * gN⁻¹ * bN⁻¹) = 1 := by
      have hc := (hρ ⟨b, hb.1⟩).eq
      simp only [map_mul, map_inv]
      rw [hgA]
      change _ * ggLAut L θ bN * _ * _ = 1 at *
      have hc' : ((MulAut.conj (θ (QuotientGroup.mk ℓ)))⁻¹ * ggLAut L θ hN') * ggLAut L θ bN =
          ggLAut L θ bN * ((MulAut.conj (θ (QuotientGroup.mk ℓ)))⁻¹ * ggLAut L θ hN') := hc
      rw [hc']; group
    exact mem_centralizer_of_ggLAut_eq_one L θ hL h1
  have hgFY := mem_sup_of_comm_mem_centralizer hS hN hgH hcomm
  have : h = (ℓ : G) * g := by rw [hg]; group
  rw [this]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_sup_right ℓ.2))
    (SetLike.le_def.mp (sup_le (le_sup_left.trans le_sup_left) le_sup_right) hgFY)

theorem torusWeylCent_at_of_tableBRk (hF : GGL48NbrFieldInput) {p : ℕ} {B Bs : Subgroup G}
    {x : G} {L D J X B₂ : Subgroup G} {d y : G} {K U U₁ : Subgroup G}
    (hS : GGFieldCaseSetup p B Bs x L D J X B₂ d y K U U₁) (hJK : J ≤ K) (hUK : U ⊓ K ≤ U₁)
    {R : Type} [Group R] {I : Set (MulAut R)} (θ : L ⧸ Subgroup.center L ≃* R)
    (hL : commutator L = ⊤) (hBsN : Bs ≤ Subgroup.normalizer (L : Set G))
    (h3 : ∀ b ∈ Bs, ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ)
    {r : ℕ} (hKG : GGTorusGenTableBRk p R I r) (hr : p ^ r ≤ Nat.card Bs) :
    ¬ p ∣ Nat.card (L ⊓ Subgroup.centralizer (L : Set G) : Subgroup G) ∧
    ∀ c ∈ L ⊓ Subgroup.centralizer
        ((Bs ⊓ Subgroup.centralizer (X : Set G) : Subgroup G) : Set G),
      (∃ k : ℕ, c ^ p ^ k = 1) →
      ∃ (S : Subgroup G) (W : Set G), IsPGroup p S ∧
        S ≤ Subgroup.centralizer ((Bs ⊓ Subgroup.centralizer (X : Set G) : Subgroup G) : Set G) ∧
        S ≤ J ∧
        W ⊆ Subgroup.normalizer ((Bs ⊓ Subgroup.centralizer (X : Set G) : Subgroup G) : Set G) ∧
        c ∈ Subgroup.closure (⋃ n ∈ W, (fun s => n * s * n⁻¹) '' (S : Set G)) := by
  have hp : p.Prime := hS.1.1.1.2.2.2.2.2.1.1
  haveI : Fact p.Prime := ⟨hp⟩
  have hsS := hS.1.1.1.2.2.2.2.2.2.1
  have hx1 : x ≠ 1 := hsS.2.2.1
  have hLx : L ≤ Subgroup.centralizer ({x} : Set G) := hsS.2.2.2.1.1
  have hcycL : ∀ S : Subgroup G, S ≤ Subgroup.centralizer (L : Set G) → IsPGroup p S →
      IsCyclic S := hsS.2.2.2.2
  have hBst := hS.1.1.2.1
  have hBsp : ∀ b ∈ Bs, b ^ p = 1 := hBst.2.1.2
  have hxBs : x ∈ Bs := hBst.1 hsS.2.1
  have hxo : orderOf x = p := orderOf_eq_prime (hBsp x hxBs) hx1
  have hBcomm : ∀ a ∈ Bs, ∀ b ∈ Bs, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hBst.2.1.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have h43 := hS.2.2.1
  have h44 := hS.2.2.2.2.2.1
  have hpre := hS.1.1.2.2.1
  set B₁ := Bs ⊓ Subgroup.centralizer (X : Set G) with hB₁
  have hxC : x ∈ Subgroup.centralizer (L : Set G) :=
    mem_centralizer_iff.mpr fun l hl => mem_centralizer_singleton_iff.mp (hLx hl)
  have hTp : IsPGroup p ↥(Bs ⊓ Subgroup.centralizer (L : Set G)) := fun t =>
    ⟨1, Subtype.ext (by simpa using hBsp _ t.2.1)⟩
  have hCx : Bs ⊓ Subgroup.centralizer (L : Set G) = zpowers x :=
    le_antisymm (GGL48TW.Cent.le_zpowers_of_isCyclic hp (hcycL _ inf_le_right hTp)
      (fun t ht => hBsp t ht.1) ⟨hxBs, hxC⟩ hx1) (zpowers_le.mpr ⟨hxBs, hxC⟩)
  have hB₁C : B₁ ⊓ Subgroup.centralizer (L : Set G) = ⊥ := by
    rw [eq_bot_iff]
    intro b hb
    have hbx : b ∈ zpowers x := hCx ▸ (⟨hb.1.1, hb.2⟩ : b ∈ Bs ⊓ Subgroup.centralizer (L : Set G))
    exact Subgroup.mem_bot.mpr (GGL48TW.Cent.eq_one_of_mem_zpowers hp hxo h43.1 hbx hb.1)
  have hDBs : D ≤ Bs := hpre.1.trans hBst.1
  have hxD : x ∈ D := hpre.2.2.2.1
  have hCD : Bs ⊓ Subgroup.centralizer (L : Set G) ≤ D := by
    rw [hCx]; exact zpowers_le.mpr hxD
  have hJc : IsComponentOf J (L ⊓ Subgroup.centralizer (D : Set G)) := hpre.2.2.2.2.2.1
  obtain ⟨hza, hc⟩ := hKG G L Bs B₁ D J d θ hBsN (tableBPosition_of_setup hS θ hL hBsN h3) hr
    (by rw [hCx]; exact Subgroup.zpowers_ne_bot.mpr hx1) inf_le_left hB₁C
    (by rw [card_bstar_eq hS, mul_comm])
    (normalizer_le_normalizer_of_ggFieldCase hS.1) hDBs hCD h44.1
    h44.2.1 hJc
  have hxB₁ : x ∈ Subgroup.centralizer (B₁ : Set G) :=
    mem_centralizer_iff.mpr fun b hb => hBcomm b hb.1 x hxBs
  have hxL : x ∉ L := by
    intro hxL
    obtain ⟨S, W, hSp, hSC, hSJ, hWN, hcl⟩ :=
      hc x ⟨hxL, hxB₁⟩ ⟨1, by rw [pow_one]; exact hBsp x hxBs⟩ (Or.inl hxC)
    exact not_mem_closure_weyl hF hS hUK hSp hSC (hSJ.trans hJK) hWN hcl
  have hZ : ¬ p ∣ Nat.card (L ⊓ Subgroup.centralizer (L : Set G) : Subgroup G) := by
    intro hdvd
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' p hdvd
    have hzo : orderOf (z : G) = p := by rw [Subgroup.orderOf_coe]; exact hz
    have hzp : (z : G) ^ p = 1 := by rw [← hzo]; exact pow_orderOf_eq_one _
    have hzBs : (z : G) ∈ Bs := hBst.2.2.2 _ (hza _ z.2 hzp) hzp
    have hzx : (z : G) ∈ zpowers x := hCx ▸ (⟨hzBs, z.2.2⟩ : (z : G) ∈ Bs ⊓ _)
    have heq : zpowers (z : G) = zpowers x := Subgroup.eq_of_le_of_card_ge (zpowers_le.mpr hzx)
      (by rw [Nat.card_zpowers, Nat.card_zpowers, hzo, hxo])
    have hxz : x ∈ zpowers (z : G) := heq ▸ mem_zpowers x
    exact hxL ((zpowers_le.mpr z.2.1) hxz)
  exact ⟨hZ, fun c hcm hcp => hc c hcm hcp (Or.inr hZ)⟩

theorem homocyclic_of_irredModTableBRk (hF : GGL48NbrFieldInput) {p : ℕ} {B Bs : Subgroup G}
    {x : G} {L D J X B₂ : Subgroup G} {d y : G} {K U U₁ : Subgroup G}
    (hS : GGFieldCaseSetup p B Bs x L D J X B₂ d y K U U₁) (h46 : GGL46 p Bs x X U U₁)
    {R : Type} [Group R] {I : Set (MulAut R)} (θ : L ⧸ Subgroup.center L ≃* R)
    (hL : commutator L = ⊤) (hBsN : Bs ≤ Subgroup.normalizer (L : Set G))
    (h3 : ∀ b ∈ Bs, ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ)
    {r : ℕ} (hKG : GGIrredModTableBRk p R I r) (hr : p ^ r ≤ Nat.card Bs) :
    GGL48Homocyclic p U₁ := by
  have hp : p.Prime := hS.1.1.1.2.2.2.2.2.1.1
  haveI : Fact p.Prime := ⟨hp⟩
  have hsS := hS.1.1.1.2.2.2.2.2.2.1
  have hx1 : x ≠ 1 := hsS.2.2.1
  have hLx : L ≤ Subgroup.centralizer ({x} : Set G) := hsS.2.2.2.1.1
  have hcycL : ∀ S : Subgroup G, S ≤ Subgroup.centralizer (L : Set G) → IsPGroup p S →
      IsCyclic S := hsS.2.2.2.2
  have hBst := hS.1.1.2.1
  have hBsp : ∀ b ∈ Bs, b ^ p = 1 := hBst.2.1.2
  have hxBs : x ∈ Bs := hBst.1 hsS.2.1
  have hxo : orderOf x = p := orderOf_eq_prime (hBsp x hxBs) hx1
  have hBcomm : ∀ a ∈ Bs, ∀ b ∈ Bs, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hBst.2.1.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have h43 := hS.2.2.1
  set B₁ := Bs ⊓ Subgroup.centralizer (X : Set G) with hB₁
  have hxC : x ∈ Subgroup.centralizer (L : Set G) :=
    mem_centralizer_iff.mpr fun l hl => mem_centralizer_singleton_iff.mp (hLx hl)
  have hTp : IsPGroup p ↥(Bs ⊓ Subgroup.centralizer (L : Set G)) := fun t =>
    ⟨1, Subtype.ext (by simpa using hBsp _ t.2.1)⟩
  have hCx : Bs ⊓ Subgroup.centralizer (L : Set G) = zpowers x :=
    le_antisymm (GGL48TW.Cent.le_zpowers_of_isCyclic hp (hcycL _ inf_le_right hTp)
      (fun t ht => hBsp t ht.1) ⟨hxBs, hxC⟩ hx1) (zpowers_le.mpr ⟨hxBs, hxC⟩)
  have hirr := hKG G L Bs θ hBsN (tableBPosition_of_setup hS θ hL hBsN h3) hr
  have h1 := ggL48AutomizerFirst_of_nbrField hF hS h46
  refine ggL48Homocyclic_of_irreducible hp.one_lt h46.1 (A := ggL48H0 x U₁) inf_le_right
    h46.2.2.2.1 ?_
  intro M hMB hM1 hMA
  set S := M ⊔ zpowers x with hSdef
  have hMx : zpowers x ≤ Subgroup.normalizer (M : Set G) :=
    zpowers_le.mpr (Subgroup.centralizer_le_normalizer _
      (mem_centralizer_iff.mpr fun m hm => hBcomm m (hMB hm).1 x hxBs))
  have hSBs : S ≤ Bs := sup_le (hMB.trans inf_le_left) (zpowers_le.mpr hxBs)
  have hNS : ggL48H0 x U₁ ⊔ Subgroup.centralizer (Bs : Set G) ≤
      Subgroup.normalizer (S : Set G) := by
    apply sup_le
    · intro a ha
      apply Subgroup.inf_normalizer_le_normalizer_sup M (zpowers x)
      exact ⟨GGL48TW.Cent.mem_normalizer_of_conj_mem (hMA a ha),
        Subgroup.centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun h hh => by
          obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
          have hxa : Commute x a := by
            have := mem_centralizer_singleton_iff.mp ha.1
            first | exact this | exact this.symm
          exact (Commute.zpow_left hxa k).eq)⟩
    · intro c hc
      apply GGL48TW.Cent.mem_normalizer_of_conj_mem
      intro s hs
      have := (mem_centralizer_iff.mp hc) s (hSBs hs)
      rw [← this]; simpa using hs
  have hSN : ∀ n ∈ L ⊓ Subgroup.normalizer (Bs : Set G), ∀ s ∈ S, n * s * n⁻¹ ∈ S := by
    intro n hn s hs
    exact (mem_normalizer_iff.mp (hNS (h1 ⟨hLx hn.1, hn.2⟩)) s).mp hs
  rw [hCx] at hirr
  rcases hirr S le_sup_right hSBs hSN with h | h
  · exfalso
    apply hM1
    rw [eq_bot_iff]
    intro m hm
    have hmx : m ∈ zpowers x := h ▸ (le_sup_left : M ≤ S) hm
    exact Subgroup.mem_bot.mpr (GGL48TW.Cent.eq_one_of_mem_zpowers hp hxo h43.1 hmx (hMB hm))
  · apply Subgroup.eq_of_le_of_card_ge hMB
    have h2 : Nat.card ((M : Set G) * (zpowers x : Set G)) ≤ Nat.card M * Nat.card (zpowers x) :=
      Set.natCard_mul_le
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left M (zpowers x) hMx, ← hSdef, h,
      Nat.card_zpowers, hxo] at h2
    change Nat.card Bs ≤ _ at h2
    rw [card_bstar_eq hS] at h2
    exact Nat.le_of_mul_le_mul_right h2 hp.pos

theorem automizerMeta_at_of_tableBRk {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J X B₂ : Subgroup G} {d y : G} {K U U₁ : Subgroup G}
    (hS : GGFieldCaseSetup p B Bs x L D J X B₂ d y K U U₁)
    (hN : Subgroup.centralizer ({x} : Set G) ≤ Subgroup.normalizer (L : Set G))
    {R : Type} [Group R] {I : Set (MulAut R)} (θ : L ⧸ Subgroup.center L ≃* R)
    (hL : commutator L = ⊤) (hBsN : Bs ≤ Subgroup.normalizer (L : Set G))
    (h3 : ∀ b ∈ Bs, ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ)
    (hZ : ¬ p ∣ Nat.card (L ⊓ Subgroup.centralizer (L : Set G) : Subgroup G))
    {r : ℕ} (hKGp : GGCoverPTableBRk p R I r) (hKGw : GGWPlusTableBRk p R I r)
    (hr : p ^ r ≤ Nat.card Bs) :
    GGL48AutomizerMetaAt p Bs x := by
  intro Mc Ec h hME hEA hCM hAM hAE hEp hh hhp hAEh
  have hsS := hS.1.1.1.2.2.2.2.2.2.1
  have hLx : L ≤ Subgroup.centralizer ({x} : Set G) := hsS.2.2.2.1.1
  have hBst := hS.1.1.2.1
  have hxBs : x ∈ Bs := hBst.1 hsS.2.1
  have hBcomm : ∀ a ∈ Bs, ∀ b ∈ Bs, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hBst.2.1.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hBsH : ∀ b ∈ Bs, b ∈ Subgroup.centralizer ({x} : Set G) := fun b hb =>
    mem_centralizer_singleton_iff.mpr (hBcomm b hb x hxBs)
  set A := Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.normalizer (Bs : Set G) with hA
  have hpos := tableBPosition_of_setup hS θ hL hBsN h3
  have hhN : h ∈ Subgroup.normalizer (L : Set G) := hN hh.1
  have hX : (MulAut.conj : R →* MulAut R).range ⊓
      Subgroup.normalizer (ggLAutImage L θ Bs : Set (MulAut R)) ≤ ggLAutImage L θ A := by
    rintro ξ ⟨⟨r, hr⟩, hξN⟩
    obtain ⟨q, rfl⟩ := θ.surjective r
    obtain ⟨ℓ, rfl⟩ := QuotientGroup.mk_surjective q
    have hℓH : (ℓ : G) ∈ Subgroup.centralizer ({x} : Set G) := hLx ℓ.2
    have hℓN : (ℓ : G) ∈ Subgroup.normalizer (L : Set G) := hN hℓH
    have hφℓ : ggLAut L θ ⟨ℓ, hℓN⟩ = ξ := by rw [ggLAut_of_mem_conj θ ℓ hℓN]; exact hr
    have hconj : ∀ b ∈ Bs ⊓ Subgroup.centralizer (X : Set G), (ℓ : G) * b * (ℓ : G)⁻¹ ∈
        Bs ⊔ (Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer (L : Set G)) := by
      intro b hb
      set bN : Subgroup.normalizer (L : Set G) := ⟨b, hBsN hb.1⟩ with hbN
      have hbE : ggLAut L θ bN ∈ ggLAutImage L θ Bs := ⟨bN, hb.1, rfl⟩
      obtain ⟨b', hb', hb'eq⟩ := (mem_normalizer_iff.mp hξN _).mp hbE
      have h2 : ggLAut L θ (b'⁻¹ * (⟨ℓ, hℓN⟩ * bN * (⟨ℓ, hℓN⟩ : Subgroup.normalizer (L : Set G))⁻¹))
          = 1 := by
        rw [map_mul, map_inv, hb'eq, map_mul, map_mul, map_inv, hφℓ]; group
      have hcL := mem_centralizer_of_ggLAut_eq_one L θ hL h2
      have hb'G : (b' : G) ∈ Bs := hb'
      have hc : (b' : G)⁻¹ * ((ℓ : G) * b * (ℓ : G)⁻¹) ∈
          Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer (L : Set G) := by
        refine ⟨?_, by simpa [hbN] using hcL⟩
        exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (hBsH _ hb'G))
          (Subgroup.mul_mem _ (Subgroup.mul_mem _ hℓH (hBsH b hb.1)) (Subgroup.inv_mem _ hℓH))
      have : (ℓ : G) * b * (ℓ : G)⁻¹ = (b' : G) * ((b' : G)⁻¹ * ((ℓ : G) * b * (ℓ : G)⁻¹)) := by
        group
      rw [this]
      exact Subgroup.mul_mem _ (mem_sup_left hb'G) (mem_sup_right hc)
    obtain ⟨o, hoY, hoN⟩ := exists_mem_normalizer_of_conj_mem_sup hS hN hℓH hconj
    have hoN' : o ∈ Subgroup.normalizer (L : Set G) := hN hoY.1
    have hoℓH : o⁻¹ * (ℓ : G) ∈ Subgroup.centralizer ({x} : Set G) :=
      mul_mem (inv_mem hoY.1) hℓH
    refine ⟨⟨o⁻¹ * ℓ, hN hoℓH⟩, ⟨hoℓH, hoN⟩, ?_⟩
    have he : (⟨o⁻¹ * ℓ, hN hoℓH⟩ : Subgroup.normalizer (L : Set G)) =
        (⟨o, hoN'⟩ : Subgroup.normalizer (L : Set G))⁻¹ * ⟨ℓ, hℓN⟩ := rfl
    rw [he, map_mul, map_inv,
      ggLAut_eq_one_of_mem_centralizer L θ (g := ⟨o, hoN'⟩) hoY.2, inv_one, one_mul, hφℓ]
  have hAN : ggLAutImage L θ A ≤ Subgroup.normalizer (ggLAutImage L θ Bs : Set (MulAut R)) := by
    rintro _ ⟨a, haA, rfl⟩
    exact ggLAut_mem_normalizer_image θ a haA.2
  have hpel : ∀ a ∈ ggLAutImage L θ A, (∃ k : ℕ, a ^ p ^ k = 1) →
      a ∈ (MulAut.conj : R →* MulAut R).range ⊔
        Subgroup.centralizer (ggLAutImage L θ Bs : Set (MulAut R)) := by
    rintro a - ⟨k, hk⟩
    obtain ⟨ρ, hρ⟩ := hKGp G L Bs θ hBsN hpos hr a ⟨k, hk⟩
    have hcC : (MulAut.conj ρ)⁻¹ * a ∈
        Subgroup.centralizer (ggLAutImage L θ Bs : Set (MulAut R)) := by
      rw [mem_centralizer_iff]
      rintro _ ⟨b, hb, rfl⟩
      exact (hρ ⟨b, hb⟩).eq.symm
    have : a = MulAut.conj ρ * ((MulAut.conj ρ)⁻¹ * a) := by group
    rw [this]
    exact mul_mem (mem_sup_left ⟨ρ, rfl⟩) (mem_sup_right hcC)
  have hMÊ : ggLAutImage L θ Mc ≤ ggLAutImage L θ Ec := by
    rintro _ ⟨m, hm, rfl⟩; exact ⟨m, hME hm, rfl⟩
  have hÊÂ : ggLAutImage L θ Ec ≤ ggLAutImage L θ A := by
    rintro _ ⟨e, he, rfl⟩; exact ⟨e, hEA he, rfl⟩
  have hCM' : ggLAutImage L θ A ⊓ Subgroup.centralizer (ggLAutImage L θ Bs : Set (MulAut R)) ≤
      ggLAutImage L θ Mc := by
    rintro _ ⟨⟨a, haA, rfl⟩, hac⟩
    exact ⟨a, hCM ⟨haA, mem_centralizer_of_ggLAut_mem hS θ hL hBsN a haA hac⟩, rfl⟩
  have hÂM : ggLAutImage L θ A ≤ Subgroup.normalizer (ggLAutImage L θ Mc : Set (MulAut R)) := by
    rintro _ ⟨a, haA, rfl⟩
    exact ggLAut_mem_normalizer_image θ a (hAM haA)
  have hÂE : ggLAutImage L θ A ≤ Subgroup.normalizer (ggLAutImage L θ Ec : Set (MulAut R)) := by
    rintro _ ⟨a, haA, rfl⟩
    exact ggLAut_mem_normalizer_image θ a (hAE haA)
  have hEp' : ∀ e ∈ ggLAutImage L θ Ec, ∃ k : ℕ, e ^ p ^ k ∈ ggLAutImage L θ Mc := by
    rintro _ ⟨e, he, rfl⟩
    obtain ⟨k, hk⟩ := hEp e he
    refine ⟨k, e ^ p ^ k, ?_, map_pow _ _ _⟩
    show ((e ^ p ^ k : Subgroup.normalizer (L : Set G)) : G) ∈ Mc
    rw [SubgroupClass.coe_pow]; exact hk
  have hcop : (orderOf (ggLAut L θ ⟨h, hhN⟩)).Coprime p := by
    have h1 : orderOf (ggLAut L θ ⟨h, hhN⟩) ∣ orderOf h := by
      have := orderOf_map_dvd (ggLAut L θ) (⟨h, hhN⟩ : Subgroup.normalizer (L : Set G))
      rwa [← Subgroup.orderOf_coe] at this
    exact Nat.Coprime.coprime_dvd_left h1 hhp
  have hÂEh : ggLAutImage L θ A ≤ ggLAutImage L θ Ec ⊔ zpowers (ggLAut L θ ⟨h, hhN⟩) := by
    rintro _ ⟨a, haA, rfl⟩
    have hhE : zpowers h ≤ Subgroup.normalizer (Ec : Set G) := zpowers_le.mpr (hAE hh)
    have ha' : (a : G) ∈ (Ec : Set G) * (zpowers h : Set G) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left Ec (zpowers h) hhE]; exact hAEh haA
    obtain ⟨e, he, t, ht, het⟩ := ha'
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp ht
    have heN : e ∈ Subgroup.normalizer (L : Set G) := hN (hEA he).1
    have : a = (⟨e, heN⟩ : Subgroup.normalizer (L : Set G)) * (⟨h, hhN⟩ ^ j) := by
      apply Subtype.ext
      rw [Subgroup.coe_mul, SubgroupClass.coe_zpow]
      exact het.symm
    rw [this, map_mul, map_zpow]
    exact mul_mem (mem_sup_left ⟨⟨e, heN⟩, he, rfl⟩) (mem_sup_right (zpow_mem (mem_zpowers _) j))
  have key := hKGw G L Bs θ hBsN hpos hr hZ (ggLAutImage L θ A) (ggLAutImage L θ Mc)
    (ggLAutImage L θ Ec) (ggLAut L θ ⟨h, hhN⟩) hX hAN hpel hMÊ hÊÂ hCM' hÂM hÂE hEp'
    ⟨⟨h, hhN⟩, hh, rfl⟩ hcop hÂEh
  intro e he
  have heN : e ∈ Subgroup.normalizer (L : Set G) := hN (hEA he).1
  obtain ⟨m, hm, hme⟩ := key ⟨⟨e, heN⟩, he, rfl⟩
  have hmA : (m : G) ∈ A := hEA (hME hm)
  set a : Subgroup.normalizer (L : Set G) := m⁻¹ * ⟨e, heN⟩ with ha
  have haA : (a : G) ∈ A := mul_mem (inv_mem hmA) (hEA he)
  have ha1 : ggLAut L θ a = 1 := by rw [ha, map_mul, map_inv, hme, inv_mul_cancel]
  have haC := mem_centralizer_of_ggLAut_mem hS θ hL hBsN a haA (by rw [ha1]; exact one_mem _)
  have haM : (a : G) ∈ Mc := hCM ⟨haA, haC⟩
  have : e = (m : G) * a := by
    show e = (m : G) * ((m : G)⁻¹ * e); group
  rw [this]
  exact mul_mem hm haM

theorem ggL48F4TwoThree_pow_five_le_card (hb : GGL48F4TwoThreeConfigInput) {B Bs : Subgroup G}
    {x : G} {L : Subgroup G} (hT : GGThmIHyp 3 B x L) (hBst : GGBstar 3 B Bs)
    (h4 : 3 ^ 4 ≤ Nat.card Bs)
    (hmark : LargeEvenMarking L fun lab _ _ _ _ _ => lab.tag = .F4 ∧ lab.n = 1) :
    3 ^ 5 ≤ Nat.card Bs := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hBsp : ∀ b ∈ Bs, b ^ 3 = 1 := hBst.2.1.2
  have hp3 : IsPGroup 3 Bs := fun b => ⟨1, Subtype.ext (by simpa using hBsp _ b.2)⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hp3
  by_contra h5
  push Not at h5
  have h1 : 3 ^ 4 ≤ 3 ^ n := hn ▸ h4
  have h2 : 3 ^ n < 3 ^ 5 := hn ▸ h5
  have hn4 : n = 4 := by
    have := (Nat.pow_le_pow_iff_right (by norm_num)).mp h1
    have := (Nat.pow_lt_pow_iff_right (by norm_num)).mp h2
    omega
  exact hb G B Bs x L hT hBst (hn.trans (by rw [hn4])) hmark

end CFSG.StandardType

end
