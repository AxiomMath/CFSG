module

public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL43Hard
public import CFSG.LocalAnalysis.StandardType.GGCorFourTwoTableB

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

section Defs

variable {G : Type} [Group G] [Finite G]

@[expose] def GGTableBIrred (Bs : Subgroup G) (x : G) (L : Subgroup G) : Prop :=
  (∀ S : Subgroup G, Subgroup.zpowers x ≤ S → S ≤ Bs →
      (∀ n ∈ L ⊓ Subgroup.normalizer (Bs : Set G), ∀ s ∈ S, n * s * n⁻¹ ∈ S) →
      S = Subgroup.zpowers x ∨ S = Bs) ∧
    (∃ n ∈ L ⊓ Subgroup.normalizer (Bs : Set G), ∃ b ∈ Bs, n * b ≠ b * n) ∧
    ∀ H : Subgroup G, H ≤ Bs →
      (∀ n ∈ L ⊓ Subgroup.normalizer (Bs : Set G), ∀ h ∈ H, n * h * n⁻¹ ∈ H) →
      H ⊔ Subgroup.zpowers x = Bs → H ⊓ Subgroup.zpowers x = ⊥ →
      ∀ φ : G → G, (∀ h ∈ H, φ h ∈ H) → (∀ h ∈ H, ∀ h' ∈ H, φ (h * h') = φ h * φ h') →
        (∀ n ∈ L ⊓ Subgroup.normalizer (Bs : Set G), ∀ h ∈ H, φ (n * h * n⁻¹) = n * φ h * n⁻¹) →
        ∃ c : ℕ, ∀ h ∈ H, φ h = h ^ c

end Defs

section General

variable {G : Type*} [Group G] [Finite G]

theorem exists_not_mem_zpowers_conj_mem {p : ℕ} [Fact p.Prime] {Bs Y : Subgroup G} {x : G}
    (hBs : IsElemAbelian p Bs) (hxBs : x ∈ Bs) (hcard : p ^ 2 ≤ Nat.card Bs)
    (hYx : Y ≤ Subgroup.centralizer ({x} : Set G))
    (hYN : Y ≤ Subgroup.normalizer (Bs : Set G))
    (hYp : ∀ g ∈ Y, ∃ k : ℕ, g ^ p ^ k ∈ Subgroup.centralizer (Bs : Set G)) :
    ∃ b ∈ Bs, b ∉ Subgroup.zpowers x ∧ ∀ g ∈ Y, g * b * g⁻¹ * b⁻¹ ∈ Subgroup.zpowers x := by
  classical
  have hp := (Fact.out : p.Prime)
  set A : Subgroup (MulAut Bs) :=
    (Y.subgroupOf (Subgroup.normalizer (Bs : Set G))).map Bs.normalizerMonoidHom with hAdef
  have hA : IsPGroup p A := by
    rintro ⟨a, g, hg, rfl⟩
    obtain ⟨k, hk⟩ := hYp g (Subgroup.mem_subgroupOf.mp hg)
    refine ⟨k, Subtype.ext ?_⟩
    have hker : g ^ p ^ k ∈ Bs.normalizerMonoidHom.ker := by
      rw [Subgroup.normalizerMonoidHom_ker]
      exact Subgroup.mem_subgroupOf.mpr (by simpa using hk)
    simpa [map_pow] using hker
  set Z : Subgroup Bs := (Subgroup.zpowers x).subgroupOf Bs with hZdef
  have hcomm : ∀ a b : Bs, a * b = b * a := fun a b =>
    Subtype.ext (mul_comm_of_isElemAbelian hBs a.2 b.2)
  have hZn : Z.Normal := ⟨fun n _ g => by rwa [hcomm g n, mul_inv_cancel_right]⟩
  have hAZ : ∀ a ∈ A, ∀ z : Bs, z ∈ Z → (a : MulAut Bs) z = z := by
    rintro _ ⟨g, hg, rfl⟩ z hz
    apply Subtype.ext
    change (g : G) * z * (g : G)⁻¹ = z
    have hgx : (g : G) * x = x * g :=
      Subgroup.mem_centralizer_singleton_iff.mp (hYx (Subgroup.mem_subgroupOf.mp hg))
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (Subgroup.mem_subgroupOf.mp hz)
    rw [← hk, ← conj_zpow, hgx, mul_inv_cancel_right]
  have : MulAction.QuotientAction A Z := ⟨fun a b c h => by
    have h' : (a : MulAut Bs) (b⁻¹ * c) = b⁻¹ * c := hAZ a a.2 _ h
    change ((a : MulAut Bs) b)⁻¹ * (a : MulAut Bs) c ∈ Z
    rw [← map_inv, ← map_mul, h']
    exact h⟩
  have hpQ : p ∣ Nat.card (Bs ⧸ Z) := by
    by_contra hnd
    have hBsp : IsPGroup p Bs := fun g => ⟨1, Subtype.ext (by simpa using hBs.2 g g.2)⟩
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hBsp
    have hprod := Subgroup.card_eq_card_quotient_mul_card_subgroup Z
    have hQdvd : Nat.card (Bs ⧸ Z) ∣ p ^ n := ⟨Nat.card Z, by rw [← hn, hprod]⟩
    have hQ1 : Nat.card (Bs ⧸ Z) = 1 :=
      Nat.Coprime.eq_one_of_dvd ((Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp).mpr
        hnd)).pow_right n) hQdvd
    have hZp : Nat.card Z ≤ p := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Subgroup.zpowers_le.mpr hxBs)).toEquiv,
        Nat.card_zpowers]
      exact Nat.le_of_dvd hp.pos (orderOf_dvd_of_pow_eq_one (hBs.2 x hxBs))
    rw [hQ1, one_mul] at hprod
    have : p ^ 2 ≤ p := hcard.trans (hprod ▸ hZp)
    nlinarith [hp.two_le]
  have h1 : (1 : Bs ⧸ Z) ∈ MulAction.fixedPoints A (Bs ⧸ Z) := fun a => by
    rw [← QuotientGroup.mk_one, MulAction.Quotient.smul_mk]
    congr 1
    exact map_one (a : MulAut Bs)
  obtain ⟨q, hq, hq1⟩ := hA.exists_fixed_point_of_prime_dvd_card_of_fixed_point (Bs ⧸ Z) hpQ h1
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective q
  refine ⟨b, b.2, fun hb => hq1 ?_, fun g hg => ?_⟩
  · exact ((QuotientGroup.eq_one_iff b).mpr (Subgroup.mem_subgroupOf.mpr hb)).symm
  · have hgA : Bs.normalizerMonoidHom ⟨g, hYN hg⟩ ∈ A :=
      ⟨⟨g, hYN hg⟩, Subgroup.mem_subgroupOf.mpr hg, rfl⟩
    have hfix := hq ⟨_, hgA⟩
    change ((⟨_, hgA⟩ : A) • (b : Bs ⧸ Z)) = (b : Bs ⧸ Z) at hfix
    rw [MulAction.Quotient.smul_mk, QuotientGroup.eq] at hfix
    have hval : ((g : G) * b * (g : G)⁻¹)⁻¹ * b ∈ Subgroup.zpowers x :=
      Subgroup.mem_subgroupOf.mp hfix
    have hgb : (g : G) * b * (g : G)⁻¹ ∈ Bs :=
      (Subgroup.mem_normalizer_iff.mp (hYN hg) b).mp b.2
    have hc : (g : G) * b * (g : G)⁻¹ * (b : G)⁻¹ =
        (((g : G) * b * (g : G)⁻¹)⁻¹ * b)⁻¹ := by
      rw [mul_inv_rev, inv_inv]
      exact mul_comm_of_isElemAbelian hBs hgb (Bs.inv_mem b.2)
    rw [hc]
    exact Subgroup.inv_mem _ hval

end General

section Irred

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem ggTableBModule_of_irred {p : ℕ} (hp : 0 < p) {Bs L : Subgroup G} {x : G}
    (hxBs : x ∈ Bs) (hirr : GGTableBIrred Bs x L) : GGTableBModule p Bs x L Bs := by
  obtain ⟨hS, -, -⟩ := hirr
  refine ⟨hxBs, le_rfl, Nat.le_mul_of_pos_left _ hp,
    fun n hn s hs => (Subgroup.mem_normalizer_iff.mp hn.2 s).mp hs, hS, ?_⟩
  intro S T hxS hxT hSinv hTinv hST hsup
  have hSB : S ≤ Bs := hsup ▸ le_sup_left
  have hTB : T ≤ Bs := hsup ▸ le_sup_right
  rcases hS S hxS hSB hSinv with h | h
  · exact Or.inl h
  · rcases hS T hxT hTB hTinv with h' | h'
    · exact Or.inr h'
    · left
      rw [← hST, h, h', inf_idem]

omit [Finite G] in
theorem eq_of_ggTableBModule_of_irred {p : ℕ} (hp : 0 < p) {Bs L B₂ : Subgroup G} {x : G}
    (hx : x ^ p = 1) (hcard : p ^ 2 < Nat.card Bs) (hirr : GGTableBIrred Bs x L)
    (hM : GGTableBModule p Bs x L B₂) : B₂ = Bs := by
  obtain ⟨hxB₂, hB₂Bs, hcardB₂, hinv, -, -⟩ := hM
  rcases hirr.1 B₂ (Subgroup.zpowers_le.mpr hxB₂) hB₂Bs hinv with h | h
  · exfalso
    rw [h, Nat.card_zpowers] at hcardB₂
    have hox : orderOf x ≤ p := Nat.le_of_dvd hp (orderOf_dvd_of_pow_eq_one hx)
    have : p * orderOf x ≤ p * p := Nat.mul_le_mul_left p hox
    nlinarith
  · exact h

theorem ggTableBAction_of_irred {p : ℕ} (hp : 0 < p) {Bs L B₂ : Subgroup G} {x : G}
    (hBs : IsElemAbelian p Bs) (hxBs : x ∈ Bs) (hLx : L ≤ Subgroup.centralizer ({x} : Set G))
    (hcard : p ^ 2 < Nat.card Bs) (hirr : GGTableBIrred Bs x L)
    (hM : GGTableBModule p Bs x L B₂) : GGTableBAction Bs x L B₂ := by
  have hB₂ := eq_of_ggTableBModule_of_irred hp (hBs.2 x hxBs) hcard hirr hM
  subst hB₂
  obtain ⟨hS, ⟨n₀, hn₀, b₀, hb₀, hnb₀⟩, hEnd⟩ := hirr
  have hnx : ∀ n ∈ L ⊓ Subgroup.normalizer (B₂ : Set G), Commute n x := fun n hn =>
    Subgroup.mem_centralizer_singleton_iff.mp (hLx hn.1)
  refine ⟨?_, fun H hHB hHinv hHsup hHinf => ⟨?_, hEnd H hHB hHinv hHsup hHinf⟩⟩
  · intro v hv hvN
    set C : Subgroup G := B₂ ⊓ Subgroup.centralizer
      ((L ⊓ Subgroup.normalizer (B₂ : Set G) : Subgroup G) : Set G) with hC
    have hxC : Subgroup.zpowers x ≤ C := Subgroup.zpowers_le.mpr
      ⟨hxBs, Subgroup.mem_centralizer_iff.mpr fun n hn => (hnx n hn).eq⟩
    have hCinv : ∀ n ∈ L ⊓ Subgroup.normalizer (B₂ : Set G), ∀ c ∈ C, n * c * n⁻¹ ∈ C := by
      intro n hn c hc
      rw [Subgroup.mem_centralizer_iff.mp hc.2 n hn, mul_inv_cancel_right]
      exact hc
    rcases hS C hxC inf_le_left hCinv with h | h
    · rw [← h]
      exact ⟨hv, Subgroup.mem_centralizer_iff.mpr fun n hn => hvN n hn⟩
    · exfalso
      have hb₀C : b₀ ∈ C := h ▸ hb₀
      exact hnb₀ (Subgroup.mem_centralizer_iff.mp hb₀C.2 n₀ hn₀)
  · intro n hn v hv
    have hxH : ∀ h ∈ H, x * h = h * x := fun h hh =>
      mul_comm_of_isElemAbelian hBs hxBs (hHB hh)
    obtain ⟨h, hh, j, rfl⟩ := exists_mem_mul_pow_of_mem_sup hxH (hHsup ▸ hv)
    have c : Commute n (x ^ j) := (hnx n hn).pow_right j
    have e : n * (h * x ^ j) * n⁻¹ * (h * x ^ j)⁻¹ = n * h * n⁻¹ * h⁻¹ := by
      calc n * (h * x ^ j) * n⁻¹ * (h * x ^ j)⁻¹
          = n * h * (x ^ j * n⁻¹) * (x ^ j)⁻¹ * h⁻¹ := by group
        _ = n * h * (n⁻¹ * x ^ j) * (x ^ j)⁻¹ * h⁻¹ := by rw [← c.inv_left.eq]
        _ = n * h * n⁻¹ * h⁻¹ := by group
    rw [e]
    exact H.mul_mem (hHinv n hn h hh) (H.inv_mem hh)

theorem tableBCx_of_irred {p : ℕ} [Fact p.Prime] {Bs L Y : Subgroup G} {x : G}
    (hBs : IsElemAbelian p Bs) (hxBs : x ∈ Bs) (hLx : L ≤ Subgroup.centralizer ({x} : Set G))
    (hcard : p ^ 2 ≤ Nat.card Bs) (hirr : GGTableBIrred Bs x L)
    (hYx : Y ≤ Subgroup.centralizer ({x} : Set G))
    (hYN : Y ≤ Subgroup.normalizer (Bs : Set G))
    (hYn : ∀ n ∈ Subgroup.normalizer (Bs : Set G) ⊓ Subgroup.centralizer ({x} : Set G),
      ∀ g ∈ Y, n * g * n⁻¹ ∈ Y)
    (hYp : ∀ g ∈ Y, ∃ k : ℕ, g ^ p ^ k ∈ Subgroup.centralizer (Bs : Set G)) :
    ∀ g ∈ Y, ∀ b ∈ Bs, g * b * g⁻¹ * b⁻¹ ∈ Subgroup.zpowers x := by
  have hgBs : ∀ g ∈ Y, ∀ b ∈ Bs, g * b * g⁻¹ ∈ Bs := fun g hg b hb =>
    (Subgroup.mem_normalizer_iff.mp (hYN hg) b).mp hb
  let F : Subgroup G :=
    { carrier := {b | b ∈ Bs ∧ ∀ g ∈ Y, g * b * g⁻¹ * b⁻¹ ∈ Subgroup.zpowers x}
      mul_mem' := by
        rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
        refine ⟨Bs.mul_mem ha hb, fun g hg => ?_⟩
        have e : g * (a * b) * g⁻¹ * (a * b)⁻¹ =
            (g * a * g⁻¹ * a⁻¹) * (g * b * g⁻¹ * b⁻¹) := by
          have h1 : a⁻¹ * (g * b * g⁻¹) = (g * b * g⁻¹) * a⁻¹ :=
            mul_comm_of_isElemAbelian hBs (Bs.inv_mem ha) (hgBs g hg b hb)
          have h2 : b⁻¹ * a⁻¹ = a⁻¹ * b⁻¹ :=
            mul_comm_of_isElemAbelian hBs (Bs.inv_mem hb) (Bs.inv_mem ha)
          calc g * (a * b) * g⁻¹ * (a * b)⁻¹
              = (g * a * g⁻¹) * (g * b * g⁻¹) * (b⁻¹ * a⁻¹) := by group
            _ = (g * a * g⁻¹) * (g * b * g⁻¹) * (a⁻¹ * b⁻¹) := by rw [h2]
            _ = (g * a * g⁻¹) * ((g * b * g⁻¹) * a⁻¹) * b⁻¹ := by group
            _ = (g * a * g⁻¹) * (a⁻¹ * (g * b * g⁻¹)) * b⁻¹ := by rw [h1]
            _ = (g * a * g⁻¹ * a⁻¹) * (g * b * g⁻¹ * b⁻¹) := by group
        rw [e]
        exact Subgroup.mul_mem _ (ha' g hg) (hb' g hg)
      one_mem' := ⟨Bs.one_mem, fun g _ => by simp⟩
      inv_mem' := by
        rintro a ⟨ha, ha'⟩
        refine ⟨Bs.inv_mem ha, fun g hg => ?_⟩
        have e : g * a⁻¹ * g⁻¹ * a⁻¹⁻¹ = (g * a * g⁻¹ * a⁻¹)⁻¹ := by
          have h1 : (g * a * g⁻¹)⁻¹ * a = a * (g * a * g⁻¹)⁻¹ :=
            mul_comm_of_isElemAbelian hBs (Bs.inv_mem (hgBs g hg a ha)) ha
          calc g * a⁻¹ * g⁻¹ * a⁻¹⁻¹ = (g * a * g⁻¹)⁻¹ * a := by group
            _ = a * (g * a * g⁻¹)⁻¹ := h1
            _ = (g * a * g⁻¹ * a⁻¹)⁻¹ := by group
        rw [e]
        exact Subgroup.inv_mem _ (ha' g hg) }
  have hxF : Subgroup.zpowers x ≤ F := by
    rw [Subgroup.zpowers_le]
    refine ⟨hxBs, fun g hg => ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff.mp (hYx hg), mul_inv_cancel_right,
      mul_inv_cancel]
    exact Subgroup.one_mem _
  have hFinv : ∀ n ∈ L ⊓ Subgroup.normalizer (Bs : Set G), ∀ s ∈ F, n * s * n⁻¹ ∈ F := by
    rintro n hn s ⟨hs, hs'⟩
    have hnx : Commute n x := Subgroup.mem_centralizer_singleton_iff.mp (hLx hn.1)
    refine ⟨(Subgroup.mem_normalizer_iff.mp hn.2 s).mp hs, fun g hg => ?_⟩
    have hn' : n⁻¹ ∈ Subgroup.normalizer (Bs : Set G) ⊓ Subgroup.centralizer ({x} : Set G) :=
      ⟨Subgroup.inv_mem _ hn.2, Subgroup.inv_mem _ (hLx hn.1)⟩
    have hg' : n⁻¹ * g * n⁻¹⁻¹ ∈ Y := hYn _ hn' g hg
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hs' _ hg')
    have e : g * (n * s * n⁻¹) * g⁻¹ * (n * s * n⁻¹)⁻¹ =
        n * ((n⁻¹ * g * n⁻¹⁻¹) * s * (n⁻¹ * g * n⁻¹⁻¹)⁻¹ * s⁻¹) * n⁻¹ := by group
    rw [e, ← hk, ← conj_zpow, hnx.eq, mul_inv_cancel_right]
    exact Subgroup.zpow_mem_zpowers x k
  rcases hirr.1 F hxF (fun b hb => hb.1) hFinv with h | h
  · exfalso
    obtain ⟨b, hb, hbx, hbY⟩ := exists_not_mem_zpowers_conj_mem hBs hxBs hcard hYx hYN hYp
    have hbF : b ∈ F := ⟨hb, hbY⟩
    rw [h] at hbF
    exact hbx hbF
  · intro g hg b hb
    have hbF : b ∈ F := h ▸ hb
    exact hbF.2 g hg

end Irred

section On

variable {G : Type} [Group G] [Finite G]

@[expose] def GGTableBIrredInputOn (S : ℕ → LargeEvenLabel → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGConfig p B Bs x L D J → GGInnerDiagOnLab S p Bs L → GGTableBIrred Bs x L

@[expose] def GGTableBCxInputOn (S : ℕ → LargeEvenLabel → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGConfig p B Bs x L D J → GGInnerDiagOnLab S p B L →
    ∀ Y : Subgroup G, Y ≤ Subgroup.centralizer ({x} : Set G) →
      Y ≤ Subgroup.normalizer (Bs : Set G) → Subgroup.centralizer (Bs : Set G) ≤ Y →
      (∀ n ∈ Subgroup.normalizer (Bs : Set G) ⊓ Subgroup.centralizer ({x} : Set G), ∀ g ∈ Y,
        n * g * n⁻¹ ∈ Y) →
      (∀ g ∈ Y, ∃ k : ℕ, g ^ p ^ k ∈ Subgroup.centralizer (Bs : Set G)) →
      ∀ g ∈ Y, ∀ b ∈ Bs, g * b * g⁻¹ * b⁻¹ ∈ Subgroup.zpowers x

@[expose] def GGTableBModuleInputOn (S : ℕ → LargeEvenLabel → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGConfig p B Bs x L D J → GGInnerDiagOnLab S p B L →
      ∃ B₂ : Subgroup G, GGTableBModule p Bs x L B₂

@[expose] def GGTableBActionInputOn (S : ℕ → LargeEvenLabel → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J B₂ : Subgroup G),
    GGConfig p B Bs x L D J → GGInnerDiagOnLab S p B L → GGTableBModule p Bs x L B₂ →
      GGTableBAction Bs x L B₂

theorem GGConfig.tableB_facts {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J) :
    p.Prime ∧ IsElemAbelian p Bs ∧ x ∈ Bs ∧ L ≤ Subgroup.centralizer ({x} : Set G) ∧
      p ^ 4 ≤ Nat.card Bs := by
  have hp : p.Prime := hcfg.1.2.2.2.2.2.1.1
  refine ⟨hp, hcfg.2.1.2.1, hcfg.2.1.1 hcfg.1.2.2.2.2.2.2.1.2.1,
    hcfg.1.2.2.2.2.2.2.1.2.2.2.1.1, ?_⟩
  have hBc : Nat.card B = p ^ LargeEvenTwoLocalRank p G := hcfg.1.2.2.2.2.2.2.1.1.2.1
  have h4 : 4 ≤ LargeEvenTwoLocalRank p G := hcfg.1.2.2.2.2.2.1.2.2.2
  calc p ^ 4 ≤ p ^ LargeEvenTwoLocalRank p G := Nat.pow_le_pow_right hp.pos h4
    _ = Nat.card B := hBc.symm
    _ ≤ Nat.card Bs := Subgroup.card_le_of_le hcfg.2.1.1

theorem GGConfig.sq_lt_card {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J) : p ^ 2 < Nat.card Bs := by
  obtain ⟨hp, -, -, -, h4⟩ := hcfg.tableB_facts
  exact (Nat.pow_lt_pow_right hp.one_lt (by norm_num : 2 < 4)).trans_le h4

theorem ggTableBCxInputOn_of_irred {S : ℕ → LargeEvenLabel → Prop}
    (hD : GGBstarInnerDiagLInputOn S) (h : GGTableBIrredInputOn S) : GGTableBCxInputOn S := by
  intro G _ _ p B Bs x L D J hcfg hM Y hYx hYN _ hYn hYp
  obtain ⟨hp, hBs, hxBs, hLx, -⟩ := hcfg.tableB_facts
  have := Fact.mk hp
  exact tableBCx_of_irred hBs hxBs hLx hcfg.sq_lt_card.le
    (h G p B Bs x L D J hcfg (hD G p B Bs x L D J hcfg hM)) hYx hYN hYn hYp

theorem ggTableBModuleInputOn_of_irred {S : ℕ → LargeEvenLabel → Prop}
    (hD : GGBstarInnerDiagLInputOn S) (h : GGTableBIrredInputOn S) : GGTableBModuleInputOn S := by
  intro G _ _ p B Bs x L D J hcfg hM
  obtain ⟨hp, -, hxBs, -, -⟩ := hcfg.tableB_facts
  exact ⟨Bs, ggTableBModule_of_irred hp.pos hxBs
    (h G p B Bs x L D J hcfg (hD G p B Bs x L D J hcfg hM))⟩

theorem ggTableBActionInputOn_of_irred {S : ℕ → LargeEvenLabel → Prop}
    (hD : GGBstarInnerDiagLInputOn S) (h : GGTableBIrredInputOn S) : GGTableBActionInputOn S := by
  intro G _ _ p B Bs x L D J B₂ hcfg hM hMod
  obtain ⟨hp, hBs, hxBs, hLx, -⟩ := hcfg.tableB_facts
  exact ggTableBAction_of_irred hp.pos hBs hxBs hLx hcfg.sq_lt_card
    (h G p B Bs x L D J hcfg (hD G p B Bs x L D J hcfg hM)) hMod

theorem GGTableBIrredInputOn.mono {S S' : ℕ → LargeEvenLabel → Prop}
    (hSS' : ∀ p lab, S p lab → S' p lab) (h : GGTableBIrredInputOn S') : GGTableBIrredInputOn S :=
  fun G _ _ p B Bs x L D J hcfg hM => h G p B Bs x L D J hcfg (hM.mono hSS')

theorem GGTableBIrredInputOn.or {S₁ S₂ : ℕ → LargeEvenLabel → Prop}
    (h₁ : GGTableBIrredInputOn S₁) (h₂ : GGTableBIrredInputOn S₂) :
    GGTableBIrredInputOn fun p lab => S₁ p lab ∨ S₂ p lab := by
  intro G _ _ p B Bs x L D J hcfg hM
  rcases hM.elim_or with hM | hM
  · exact h₁ G p B Bs x L D J hcfg hM
  · exact h₂ G p B Bs x L D J hcfg hM

theorem GGTableBCxInputOn.or {S₁ S₂ : ℕ → LargeEvenLabel → Prop} (h₁ : GGTableBCxInputOn S₁)
    (h₂ : GGTableBCxInputOn S₂) : GGTableBCxInputOn fun p lab => S₁ p lab ∨ S₂ p lab := by
  intro G _ _ p B Bs x L D J hcfg hM
  rcases hM.elim_or with hM | hM
  · exact h₁ G p B Bs x L D J hcfg hM
  · exact h₂ G p B Bs x L D J hcfg hM

theorem GGTableBModuleInputOn.or {S₁ S₂ : ℕ → LargeEvenLabel → Prop}
    (h₁ : GGTableBModuleInputOn S₁) (h₂ : GGTableBModuleInputOn S₂) :
    GGTableBModuleInputOn fun p lab => S₁ p lab ∨ S₂ p lab := by
  intro G _ _ p B Bs x L D J hcfg hM
  rcases hM.elim_or with hM | hM
  · exact h₁ G p B Bs x L D J hcfg hM
  · exact h₂ G p B Bs x L D J hcfg hM

theorem GGTableBActionInputOn.or {S₁ S₂ : ℕ → LargeEvenLabel → Prop}
    (h₁ : GGTableBActionInputOn S₁) (h₂ : GGTableBActionInputOn S₂) :
    GGTableBActionInputOn fun p lab => S₁ p lab ∨ S₂ p lab := by
  intro G _ _ p B Bs x L D J B₂ hcfg hM
  rcases hM.elim_or with hM | hM
  · exact h₁ G p B Bs x L D J B₂ hcfg hM
  · exact h₂ G p B Bs x L D J B₂ hcfg hM

theorem ggTableBCxInput_of_on {S : ℕ → LargeEvenLabel → Prop}
    (hS : ∀ p lab, LargeEvenInLambda2 lab → LargeEvenSplit p lab → S p lab)
    (h : GGTableBCxInputOn S) : GGTableBCxInput :=
  fun G _ _ p B Bs x L D J hcfg => h G p B Bs x L D J hcfg (ggInnerDiagOnLab_of_cover hS hcfg.1)

theorem ggTableBModuleInput_of_on {S : ℕ → LargeEvenLabel → Prop}
    (hS : ∀ p lab, LargeEvenInLambda2 lab → LargeEvenSplit p lab → S p lab)
    (h : GGTableBModuleInputOn S) : GGTableBModuleInput :=
  fun G _ _ p B Bs x L D J hcfg => h G p B Bs x L D J hcfg (ggInnerDiagOnLab_of_cover hS hcfg.1)

theorem ggTableBActionInput_of_on {S : ℕ → LargeEvenLabel → Prop}
    (hS : ∀ p lab, LargeEvenInLambda2 lab → LargeEvenSplit p lab → S p lab)
    (h : GGTableBActionInputOn S) : GGTableBActionInput :=
  fun G _ _ p B Bs x L D J B₂ hcfg =>
    h G p B Bs x L D J B₂ hcfg (ggInnerDiagOnLab_of_cover hS hcfg.1)

end On

end CFSG.StandardType

end
