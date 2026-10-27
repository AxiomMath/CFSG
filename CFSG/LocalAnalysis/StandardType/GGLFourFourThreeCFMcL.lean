module

public import CFSG.LocalAnalysis.StandardType.GGLFourFourThreeMarking
public import CFSG.LocalAnalysis.StandardType.GGNbrLang

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[expose] def GGNbrLangAxisInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGConfig p B Bs x L D J → ∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K →
      ∀ hN : Bs ≤ Subgroup.normalizer (K : Set G),
        GGMarkingAll (K := ↥K) fun _ _ _ I F θ =>
          (∀ (b : G) (hb : b ∈ Bs), ∃ u ∈ I, ∃ f ∈ Subgroup.closure F,
            ggLAut K θ ⟨b, hN hb⟩ = u * f) →
          ∀ (b₀ : G) (hb₀ : b₀ ∈ Bs), ggLAut K θ ⟨b₀, hN hb₀⟩ ∉ I →
            ∃ B₀ : Subgroup G, B₀ ≤ Bs ∧ Nat.card B₀ * p = Nat.card Bs ∧ b₀ ∉ B₀ ∧
              (∀ (b : G) (hb : b ∈ Bs), ggLAut K θ ⟨b, hN hb⟩ ∈ I → b ∈ B₀) ∧
              ∃ k ∈ Subgroup.centralizer (B₀ : Set G), ∃ e ∈ B₀, e ≠ 1 ∧
                k * b₀ * k⁻¹ = e * b₀

theorem ggNbrLangInput_of_axis (h : GGNbrLangAxisInput) : GGNbrLangInput := by
  intro G _ _ p B Bs x L D J hcfg y K hnbr hN P hP
  refine largeEvenMarking_mono ?_ (h G p B Bs x L D J hcfg y K hnbr hN P hP)
  rintro lab R _ I F θ ⟨hPθ, hQ⟩
  refine ⟨hPθ, fun hgr b₀ hb₀ hb₀I => ?_⟩
  obtain ⟨B₀, hB₀, hcard, hb₀', -, hk⟩ := hQ hgr b₀ hb₀ hb₀I
  exact ⟨B₀, hB₀, hcard, hb₀', hk⟩

@[expose] def GGNbrLangTorusAxisInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGConfig p B Bs x L D J → ∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K →
      ∀ hN : Bs ≤ Subgroup.normalizer (K : Set G),
        GGMarkingAll (K := ↥K) fun _ _ _ I F θ =>
          (∀ (b : G) (hb : b ∈ Bs), ∃ u ∈ I, ∃ f ∈ Subgroup.closure F,
            ggLAut K θ ⟨b, hN hb⟩ = u * f) →
          ∀ (b₀ : G) (hb₀ : b₀ ∈ Bs), ggLAut K θ ⟨b₀, hN hb₀⟩ ∉ I →
            ∃ B₀ : Subgroup G, B₀ ≤ Bs ∧ Nat.card B₀ * p = Nat.card Bs ∧ b₀ ∉ B₀ ∧
              (∀ (b : G) (hb : b ∈ Bs), ggLAut K θ ⟨b, hN hb⟩ ∈ I → b ∈ B₀) ∧
              ∃ T : Subgroup G, T ≤ Subgroup.centralizer (B₀ : Set G) ∧
                (∀ a ∈ T, ∀ c ∈ T, a * c = c * a) ∧
                b₀ ∈ Subgroup.normalizer (T : Set G) ∧
                (∀ t ∈ T, b₀ * t * b₀⁻¹ = t → ∃ s ∈ T,
                  t = ((List.range p).map fun i => b₀ ^ i * s * (b₀ ^ i)⁻¹).prod) ∧
                ∃ e ∈ B₀ ⊓ T, e ≠ 1

theorem ggNbrLangTorusInput_of_axis (h : GGNbrLangTorusAxisInput) : GGNbrLangTorusInput := by
  intro G _ _ p B Bs x L D J hcfg y K hnbr hN P hP
  refine largeEvenMarking_mono ?_ (h G p B Bs x L D J hcfg y K hnbr hN P hP)
  rintro lab R _ I F θ ⟨hPθ, hQ⟩
  refine ⟨hPθ, fun hgr b₀ hb₀ hb₀I => ?_⟩
  obtain ⟨B₀, hB₀, hcard, hb₀', -, hT⟩ := hQ hgr b₀ hb₀ hb₀I
  exact ⟨B₀, hB₀, hcard, hb₀', hT⟩

theorem ggNbrLangAxisInput_of_torus (h : GGNbrLangTorusAxisInput) : GGNbrLangAxisInput := by
  intro G _ _ p B Bs x L D J hcfg y K hK hN P hP
  refine largeEvenMarking_mono ?_ (h G p B Bs x L D J hcfg y K hK hN P hP)
  rintro lab R _ I F θ ⟨hPθ, hQ⟩
  refine ⟨hPθ, fun hall b₀ hb₀ hb₀I => ?_⟩
  obtain ⟨B₀, hB₀, hcard, hb₀', hax, T, hTC, hTab, hb₀T, hnorm, e, ⟨heB₀, heT⟩, he1⟩ :=
    hQ hall b₀ hb₀ hb₀I
  have hBs : IsElemAbelian p Bs := hcfg.2.1.2.1
  have hbp : b₀ ^ p = 1 := hBs.2 b₀ hb₀
  have heb : b₀ * e * b₀⁻¹ = e := by
    rw [TableB.IsElemAbelian.comm hBs hb₀ (hB₀ heB₀), mul_inv_cancel_right]
  have hep : e ^ p = 1 := hBs.2 e (hB₀ heB₀)
  obtain ⟨k, hkT, hk⟩ := NbrLang.exists_conj_eq_mul_of_norm hTab hb₀T hbp hnorm heT heb hep
  exact ⟨B₀, hB₀, hcard, hb₀', hax, k, hTC hkT, e, heB₀, he1, hk⟩

namespace GGL44CF

section Flag

variable {G : Type} [Group G]

@[expose] def actTrivOn (S U : Subgroup G) : Subgroup G where
  carrier := {g | g ∈ Subgroup.normalizer (S : Set G) ∧ ∀ s ∈ S, g * s * g⁻¹ * s⁻¹ ∈ U}
  mul_mem' := by
    rintro g h ⟨hgN, hg⟩ ⟨hhN, hh⟩
    refine ⟨Subgroup.mul_mem _ hgN hhN, fun s hs => ?_⟩
    have hs' : h * s * h⁻¹ ∈ S := (Subgroup.mem_normalizer_iff.mp hhN s).mp hs
    have e : g * h * s * (g * h)⁻¹ * s⁻¹ =
        (g * (h * s * h⁻¹) * g⁻¹ * (h * s * h⁻¹)⁻¹) * (h * s * h⁻¹ * s⁻¹) := by group
    rw [e]
    exact U.mul_mem (hg _ hs') (hh s hs)
  one_mem' := ⟨Subgroup.one_mem _, fun s _ => by simp⟩
  inv_mem' := by
    rintro g ⟨hgN, hg⟩
    refine ⟨Subgroup.inv_mem _ hgN, fun s hs => ?_⟩
    have hs' : g⁻¹ * s * g⁻¹⁻¹ ∈ S :=
      (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hgN) s).mp hs
    have e : g⁻¹ * s * g⁻¹⁻¹ * s⁻¹ =
        (g * (g⁻¹ * s * g⁻¹⁻¹) * g⁻¹ * (g⁻¹ * s * g⁻¹⁻¹)⁻¹)⁻¹ := by group
    rw [e]
    exact U.inv_mem (hg _ hs')

theorem mem_actTrivOn {S U : Subgroup G} {g : G} :
    g ∈ actTrivOn S U ↔
      g ∈ Subgroup.normalizer (S : Set G) ∧ ∀ s ∈ S, g * s * g⁻¹ * s⁻¹ ∈ U :=
  Iff.rfl

theorem conj_mem_actTrivOn {S U : Subgroup G} {n g : G}
    (hnS : n ∈ Subgroup.normalizer (S : Set G)) (hnU : n ∈ Subgroup.normalizer (U : Set G))
    (hg : g ∈ actTrivOn S U) : n * g * n⁻¹ ∈ actTrivOn S U := by
  obtain ⟨hgN, hgc⟩ := hg
  refine ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hnS hgN) (Subgroup.inv_mem _ hnS), fun s hs => ?_⟩
  have hs' : n⁻¹ * s * n⁻¹⁻¹ ∈ S :=
    (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hnS) s).mp hs
  have e : n * g * n⁻¹ * s * (n * g * n⁻¹)⁻¹ * s⁻¹ =
      n * (g * (n⁻¹ * s * n⁻¹⁻¹) * g⁻¹ * (n⁻¹ * s * n⁻¹⁻¹)⁻¹) * n⁻¹ := by group
  rw [e]
  exact (Subgroup.mem_normalizer_iff.mp hnU _).mp (hgc _ hs')

@[expose] def flagRadical (Bs B₁ T : Subgroup G) : Subgroup G :=
  actTrivOn Bs B₁ ⊓ actTrivOn B₁ T ⊓ Subgroup.centralizer (T : Set G)

theorem pow_conj_eq_of_commute {g s c : G} (hgs : g * s * g⁻¹ = c * s) (hc : Commute g c)
    (n : ℕ) : g ^ n * s * (g ^ n)⁻¹ = c ^ n * s := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hgc : g * c ^ n * g⁻¹ = c ^ n := by
      rw [(hc.pow_right n).eq, mul_inv_cancel_right]
    calc g ^ (n + 1) * s * (g ^ (n + 1))⁻¹ = g * (g ^ n * s * (g ^ n)⁻¹) * g⁻¹ := by group
      _ = g * (c ^ n * s) * g⁻¹ := by rw [ih]
      _ = (g * c ^ n * g⁻¹) * (g * s * g⁻¹) := by group
      _ = c ^ n * (c * s) := by rw [hgc, hgs]
      _ = c ^ (n + 1) * s := by group

theorem pow_mul_comm_of_commute {g s : G} {p : ℕ} (hc : Commute g (g * s * g⁻¹ * s⁻¹))
    (hcp : (g * s * g⁻¹ * s⁻¹) ^ p = 1) : s * g ^ p = g ^ p * s := by
  have h := pow_conj_eq_of_commute (s := s) (by group) hc p
  rw [hcp, one_mul] at h
  calc s * g ^ p = (g ^ p * s * (g ^ p)⁻¹) * g ^ p := by rw [h]
    _ = g ^ p * s := by group

theorem pow_mem_centralizer_of_flag {p : ℕ} {Bs B₁ T : Subgroup G}
    (hBs : ∀ b ∈ Bs, b ^ p = 1) (hB₁ : B₁ ≤ Bs) (hT : T ≤ B₁) {g : G}
    (hg : g ∈ flagRadical Bs B₁ T) : g ^ p ^ 2 ∈ Subgroup.centralizer (Bs : Set G) := by
  have hg2 : ∀ s ∈ B₁, g * s * g⁻¹ * s⁻¹ ∈ T :=
    (mem_actTrivOn.mp (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hg).1).2).2
  have hg3 : g ∈ Subgroup.centralizer (T : Set G) := (Subgroup.mem_inf.mp hg).2
  have hgp : ∀ u ∈ B₁, u * g ^ p = g ^ p * u := by
    intro u hu
    have hc := hg2 u hu
    refine pow_mul_comm_of_commute ?_ (hBs _ (hB₁ (hT hc)))
    exact ((Subgroup.mem_centralizer_iff.mp hg3) _ hc).symm
  have hgpR : g ^ p ∈ flagRadical Bs B₁ T := Subgroup.pow_mem _ hg p
  have hgp1 : ∀ s ∈ Bs, g ^ p * s * (g ^ p)⁻¹ * s⁻¹ ∈ B₁ :=
    (mem_actTrivOn.mp (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hgpR).1).1).2
  rw [Subgroup.mem_centralizer_iff]
  intro b hb
  have hc := hgp1 b hb
  rw [pow_two, pow_mul]
  exact pow_mul_comm_of_commute (hgp _ hc).symm (hBs _ (hB₁ hc))

theorem conj_mem_centralizer_of_mem_normalizer {T : Subgroup G} {n g : G}
    (hn : n ∈ Subgroup.normalizer (T : Set G)) (hg : g ∈ Subgroup.centralizer (T : Set G)) :
    n * g * n⁻¹ ∈ Subgroup.centralizer (T : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro t ht
  have ht' : n⁻¹ * t * n⁻¹⁻¹ ∈ T :=
    (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hn) t).mp ht
  have h := Subgroup.mem_centralizer_iff.mp hg _ ht'
  calc t * (n * g * n⁻¹) = n * ((n⁻¹ * t * n⁻¹⁻¹) * g) * n⁻¹ := by group
    _ = n * (g * (n⁻¹ * t * n⁻¹⁻¹)) * n⁻¹ := by rw [h]
    _ = n * g * n⁻¹ * t := by group

end Flag

section FlagFinite

variable {G : Type} [Group G] [Finite G]

theorem mem_normalizer_of_conj_mem {H : Subgroup G} {n : G}
    (h : ∀ b ∈ H, n * b * n⁻¹ ∈ H) : n ∈ Subgroup.normalizer (H : Set G) := by
  have hQW : H.map (MulAut.conj n).toMonoidHom ≤ H := by
    rintro _ ⟨w, hw, rfl⟩
    simpa [MulAut.conj_apply] using h w hw
  have hQeq : H.map (MulAut.conj n).toMonoidHom = H := Subgroup.eq_of_le_of_card_ge hQW
    (Subgroup.card_map_of_injective (MulAut.conj n).injective).ge
  rw [Subgroup.mem_normalizer_iff]
  intro b
  refine ⟨h b, fun hb => ?_⟩
  rw [← hQeq] at hb
  obtain ⟨w, hw, hwb⟩ := hb
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hwb
  rw [← mul_left_cancel (mul_right_cancel hwb)]
  exact hw

theorem mul_card_le_card_of_lt {p : ℕ} [Fact p.Prime] {H K : Subgroup G}
    (hK : ∀ g ∈ K, g ^ p = 1) (hHK : H < K) : p * Nat.card H ≤ Nat.card K := by
  have hp : p.Prime := Fact.out
  have hKp : IsPGroup p ↥K := fun g => ⟨1, Subtype.ext (by simpa using hK g g.2)⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hKp
  have hdvd : Nat.card H ∣ Nat.card K := Subgroup.card_dvd_of_le hHK.le
  rw [hn] at hdvd
  obtain ⟨m, hm, hm'⟩ := (Nat.dvd_prime_pow hp).mp hdvd
  have hne : m ≠ n := by
    intro h
    apply hHK.ne
    apply Subgroup.eq_of_le_of_card_ge hHK.le
    simp [hn, hm', h]
  rw [hm', hn, ← pow_succ']
  exact Nat.pow_le_pow_right hp.pos (lt_of_le_of_ne hm hne)

theorem comm_eq_pow_of_ggL43 {p : ℕ} {Bs X : Subgroup G} {x : G} (hBs : IsElemAbelian p Bs)
    (hxBs : x ∈ Bs) (h43 : GGL43 Bs x X) (h44 : GGL44i p Bs x X) {g : G} (hg : g ∈ X)
    {b : G} (hb : b ∈ Bs) : ∃ j : ℕ, g * b * g⁻¹ * b⁻¹ = (g * x * g⁻¹ * x⁻¹) ^ j := by
  have hxc : ∀ c ∈ Bs ⊓ Subgroup.centralizer (X : Set G), x * c = c * x :=
    fun c hc => mul_comm_of_isElemAbelian hBs hxBs hc.1
  have hb' : b ∈ (Bs ⊓ Subgroup.centralizer (X : Set G)) ⊔ Subgroup.zpowers x := h43.2 ▸ hb
  obtain ⟨b₁, hb₁, j, rfl⟩ := exists_mem_mul_pow_of_mem_sup hxc hb'
  refine ⟨j, ?_⟩
  have hcB : g * x * g⁻¹ * x⁻¹ ∈ Bs := (h44.2.1 g hg x hxBs).1
  have hgb₁ : g * b₁ * g⁻¹ = b₁ := by
    rw [Subgroup.mem_centralizer_iff.mp hb₁.2 g hg, mul_inv_cancel_right]
  have hgx : g * x * g⁻¹ = (g * x * g⁻¹ * x⁻¹) * x := by group
  have hcx : Commute (g * x * g⁻¹ * x⁻¹) x := mul_comm_of_isElemAbelian hBs hcB hxBs
  have hcb₁ : Commute ((g * x * g⁻¹ * x⁻¹) ^ j) b₁ :=
    mul_comm_of_isElemAbelian hBs (Bs.pow_mem hcB j) hb₁.1
  calc g * (b₁ * x ^ j) * g⁻¹ * (b₁ * x ^ j)⁻¹
      = (g * b₁ * g⁻¹) * (g * x * g⁻¹) ^ j * (x ^ j)⁻¹ * b₁⁻¹ := by rw [conj_pow]; group
    _ = b₁ * ((g * x * g⁻¹ * x⁻¹) * x) ^ j * (x ^ j)⁻¹ * b₁⁻¹ := by rw [hgb₁, ← hgx]
    _ = b₁ * (g * x * g⁻¹ * x⁻¹) ^ j * b₁⁻¹ := by rw [hcx.mul_pow]; group
    _ = (g * x * g⁻¹ * x⁻¹) ^ j := by rw [← hcb₁.eq, mul_inv_cancel_right]

omit [Finite G] in
theorem conj_mem_bOne {Bs X : Subgroup G}
    (hXn : ∀ n ∈ Subgroup.normalizer (Bs : Set G), ∀ g ∈ X, n * g * n⁻¹ ∈ X) {n : G}
    (hn : n ∈ Subgroup.normalizer (Bs : Set G)) {b : G}
    (hb : b ∈ Bs ⊓ Subgroup.centralizer (X : Set G)) :
    n * b * n⁻¹ ∈ Bs ⊓ Subgroup.centralizer (X : Set G) := by
  refine Subgroup.mem_inf.mpr ⟨(Subgroup.mem_normalizer_iff.mp hn b).mp hb.1, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro g hg
  have hg' : n⁻¹ * g * n⁻¹⁻¹ ∈ X := hXn _ (Subgroup.inv_mem _ hn) g hg
  have h := Subgroup.mem_centralizer_iff.mp hb.2 _ hg'
  calc g * (n * b * n⁻¹) = n * ((n⁻¹ * g * n⁻¹⁻¹) * b) * n⁻¹ := by group
    _ = n * (b * (n⁻¹ * g * n⁻¹⁻¹)) * n⁻¹ := by rw [h]
    _ = n * b * n⁻¹ * g := by group

theorem conj_mem_inter_of_ggL44 {p : ℕ} {Bs X B₂ : Subgroup G} {x : G}
    (hBs : IsElemAbelian p Bs) (hxBs : x ∈ Bs) (h43 : GGL43 Bs x X) (h44 : GGL44i p Bs x X)
    (hXn : ∀ n ∈ Subgroup.normalizer (Bs : Set G), ∀ g ∈ X, n * g * n⁻¹ ∈ X)
    (h44b : ∀ b : G, b ∈ Bs ⊓ Subgroup.centralizer (X : Set G) ⊓ B₂ ↔
      ∃ g ∈ X, g * x * g⁻¹ * x⁻¹ = b)
    {n : G} (hn : n ∈ Subgroup.normalizer (Bs : Set G)) {t : G}
    (ht : t ∈ Bs ⊓ Subgroup.centralizer (X : Set G) ⊓ B₂) :
    n * t * n⁻¹ ∈ Bs ⊓ Subgroup.centralizer (X : Set G) ⊓ B₂ := by
  obtain ⟨g, hg, rfl⟩ := (h44b t).1 ht
  have hg' : n * g * n⁻¹ ∈ X := hXn n hn g hg
  have hx' : n * x * n⁻¹ ∈ Bs := (Subgroup.mem_normalizer_iff.mp hn x).mp hxBs
  obtain ⟨j, hj⟩ := comm_eq_pow_of_ggL43 hBs hxBs h43 h44 hg' hx'
  have e : n * (g * x * g⁻¹ * x⁻¹) * n⁻¹ =
      (n * g * n⁻¹) * (n * x * n⁻¹) * (n * g * n⁻¹)⁻¹ * (n * x * n⁻¹)⁻¹ := by group
  rw [e, hj]
  exact Subgroup.pow_mem _ ((h44b _).2 ⟨_, hg', rfl⟩) j

theorem ggFieldCaseNoBL5_flagRadical {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J X T : Subgroup G} (hFC : GGFieldCaseNoBL5 p B Bs x L D J X)
    (h44 : GGL44i p Bs x X) (hTB₁ : T ≤ Bs ⊓ Subgroup.centralizer (X : Set G))
    (hTinv : ∀ n ∈ Subgroup.normalizer (Bs : Set G), ∀ t ∈ T, n * t * n⁻¹ ∈ T) :
    X ≤ flagRadical Bs (Bs ⊓ Subgroup.centralizer (X : Set G)) T ∧
      GGFieldCaseNoBL5 p B Bs x L D J
        (flagRadical Bs (Bs ⊓ Subgroup.centralizer (X : Set G)) T) := by
  set B₁ : Subgroup G := Bs ⊓ Subgroup.centralizer (X : Set G) with hB₁def
  have hBs : IsElemAbelian p Bs := hFC.1.2.1.2.1
  have hXn : ∀ n ∈ Subgroup.normalizer (Bs : Set G), ∀ g ∈ X, n * g * n⁻¹ ∈ X := by
    intro n hn g hg
    have := hFC.2.2.2.1.conj_mem ⟨g, hFC.2.1 hg⟩ (Subgroup.mem_subgroupOf.mpr hg) ⟨n, hn⟩
    simpa [Subgroup.mem_subgroupOf] using this
  have hB₁N : ∀ n ∈ Subgroup.normalizer (Bs : Set G), n ∈ Subgroup.normalizer (B₁ : Set G) :=
    fun n hn => mem_normalizer_of_conj_mem fun b hb => conj_mem_bOne hXn hn hb
  have hTN : ∀ n ∈ Subgroup.normalizer (Bs : Set G), n ∈ Subgroup.normalizer (T : Set G) :=
    fun n hn => mem_normalizer_of_conj_mem fun t ht => hTinv n hn t ht
  have hcen : ∀ (S U : Subgroup G) (g : G), g ∈ Subgroup.centralizer (S : Set G) →
      g ∈ actTrivOn S U := by
    intro S U g hg
    refine ⟨Subgroup.centralizer_le_normalizer _ hg, fun s hs => ?_⟩
    rw [← Subgroup.mem_centralizer_iff.mp hg s hs, mul_inv_cancel_right, mul_inv_cancel]
    exact U.one_mem
  have hXX : X ≤ flagRadical Bs B₁ T := by
    intro g hg
    have hgB₁ : g ∈ Subgroup.centralizer (B₁ : Set G) :=
      Subgroup.mem_centralizer_iff.mpr fun b hb =>
        (Subgroup.mem_centralizer_iff.mp hb.2 g hg).symm
    refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨⟨hFC.2.1 hg, fun b hb =>
      h44.2.1 g hg b hb⟩, hcen B₁ T g hgB₁⟩, ?_⟩
    exact Subgroup.mem_centralizer_iff.mpr fun t ht =>
      (Subgroup.mem_centralizer_iff.mp hgB₁ t (hTB₁ ht))
  refine ⟨hXX, hFC.1, fun g hg => (mem_actTrivOn.mp
    (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hg).1).1).1, fun g hg => ?_, ⟨fun a ha n => ?_⟩,
    fun g hg => ⟨2, pow_mem_centralizer_of_flag (fun b hb => hBs.2 b hb) inf_le_left hTB₁ hg⟩,
    fun h => hFC.2.2.2.2.2 (hXX.trans h)⟩
  ·
    have hgB₁ : g ∈ Subgroup.centralizer (B₁ : Set G) :=
      Subgroup.centralizer_le (inf_le_left : B₁ ≤ Bs) hg
    refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨hcen Bs B₁ g hg, hcen B₁ T g hgB₁⟩, ?_⟩
    exact Subgroup.centralizer_le (hTB₁.trans inf_le_left) hg
  ·
    rw [Subgroup.mem_subgroupOf] at ha ⊢
    have hn : (n : G) ∈ Subgroup.normalizer (Bs : Set G) := n.2
    obtain ⟨⟨h1, h2⟩, h3⟩ := Subgroup.mem_inf.mp ha |>.imp_left Subgroup.mem_inf.mp
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨conj_mem_actTrivOn hn (hB₁N _ hn) h1,
      conj_mem_actTrivOn (hB₁N _ hn) (hTN _ hn) h2⟩, ?_⟩
    exact conj_mem_centralizer_of_mem_normalizer (hTN _ hn) h3

theorem false_of_lang_axis {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J X B₂ : Subgroup G}
    (hL43 : ∀ X' : Subgroup G, GGFieldCaseNoBL5 p B Bs x L D J X' → GGL43 Bs x X')
    (hFC : GGFieldCaseNoBL5 p B Bs x L D J X) (hM : GGTableBModule p Bs x L B₂)
    (h43 : GGL43 Bs x X) (h44 : GGL44i p Bs x X)
    (h44b : ∀ b : G, b ∈ Bs ⊓ Subgroup.centralizer (X : Set G) ⊓ B₂ ↔
      ∃ g ∈ X, g * x * g⁻¹ * x⁻¹ = b)
    {a : G} (ha : a ∈ Bs ⊓ Subgroup.centralizer (X : Set G)) {B₀ : Subgroup G} (hB₀ : B₀ ≤ Bs)
    (hcard : Nat.card B₀ * p = Nat.card Bs) (haB₀ : a ∉ B₀)
    (hTB₀ : Bs ⊓ Subgroup.centralizer (X : Set G) ⊓ B₂ ≤ B₀) {k e : G}
    (hk : k ∈ Subgroup.centralizer (B₀ : Set G)) (he : e ∈ B₀) (he1 : e ≠ 1)
    (hka : k * a * k⁻¹ = e * a) : False := by
  have hp : p.Prime := hFC.1.1.2.2.2.2.2.1.1
  have : Fact p.Prime := ⟨hp⟩
  have hBs : IsElemAbelian p Bs := hFC.1.2.1.2.1
  have hS : LargeEvenSStar p B x L := hFC.1.1.2.2.2.2.2.2.1
  have hxBs : x ∈ Bs := hFC.1.2.1.1 hS.2.1
  have hx1 : x ≠ 1 := hS.2.2.1
  set B₁ : Subgroup G := Bs ⊓ Subgroup.centralizer (X : Set G) with hB₁def
  set T : Subgroup G := B₁ ⊓ B₂ with hTdef
  have hXn : ∀ n ∈ Subgroup.normalizer (Bs : Set G), ∀ g ∈ X, n * g * n⁻¹ ∈ X := by
    intro n hn g hg
    have := hFC.2.2.2.1.conj_mem ⟨g, hFC.2.1 hg⟩ (Subgroup.mem_subgroupOf.mpr hg) ⟨n, hn⟩
    simpa [Subgroup.mem_subgroupOf] using this
  have hTinv : ∀ n ∈ Subgroup.normalizer (Bs : Set G), ∀ t ∈ T, n * t * n⁻¹ ∈ T :=
    fun n hn t ht => conj_mem_inter_of_ggL44 hBs hxBs h43 h44 hXn h44b hn ht
  have hTB₁ : T ≤ B₁ := inf_le_left
  obtain ⟨hXX, hFC''⟩ := ggFieldCaseNoBL5_flagRadical hFC h44 hTB₁ hTinv
  have hkN : k ∈ Subgroup.normalizer (Bs : Set G) :=
    (normalizer_and_not_normalizer_of_lang hp hBs hB₀ hcard ha.1 haB₀ hk he he1 hka).1
  have hc3 : Nat.card B₁ ≤ p * Nat.card T := by
    have h := card_le_mul_card_inf (inf_le_left : B₁ ≤ Bs) hM.2.1 hM.2.2.1
    rwa [inf_comm B₂ B₁] at h
  have hlt : B₀ ⊓ B₁ < B₁ := by
    refine lt_of_le_of_ne inf_le_right fun h => haB₀ ?_
    have h' : a ∈ B₀ ⊓ B₁ := by rw [h]; exact ha
    exact (Subgroup.mem_inf.mp h').1
  have hc5 : p * Nat.card (B₀ ⊓ B₁ : Subgroup G) ≤ Nat.card B₁ :=
    mul_card_le_card_of_lt (fun g hg => hBs.2 g (Subgroup.mem_inf.mp hg).1) hlt
  have hTeq : T = B₀ ⊓ B₁ := Subgroup.eq_of_le_of_card_ge (le_inf hTB₀ hTB₁)
    (Nat.le_of_mul_le_mul_left (hc5.trans hc3) hp.pos)
  have heB₁ : e ∈ B₁ := by
    have h1 : k * a * k⁻¹ ∈ B₁ := conj_mem_bOne hXn hkN ha
    have h2 : e = k * a * k⁻¹ * a⁻¹ := by rw [hka]; group
    rw [h2]
    exact B₁.mul_mem h1 (B₁.inv_mem ha)
  have heT : e ∈ T := by
    rw [hTeq]
    exact Subgroup.mem_inf.mpr ⟨he, heB₁⟩
  have hkb : ∀ b ∈ Bs, k * b * k⁻¹ * b⁻¹ ∈ T := by
    intro b hb
    obtain ⟨b₁, hb₁, j, rfl⟩ :=
      NbrFieldLang.exists_mul_pow_of_card hp hBs hB₀ hcard ha.1 haB₀ hb
    rw [NbrFieldLang.conj_mul_pow_of_lang hBs hB₀ ha.1 hk he hka hb₁ j, mul_inv_cancel_right]
    exact T.pow_mem heT j
  have hkX : k ∈ flagRadical Bs B₁ T := by
    refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨⟨hkN, fun b hb => hTB₁ (hkb b hb)⟩,
      ⟨mem_normalizer_of_conj_mem fun b hb => conj_mem_bOne hXn hkN hb,
        fun b hb => hkb b (Subgroup.mem_inf.mp hb).1⟩⟩, ?_⟩
    exact Subgroup.mem_centralizer_iff.mpr fun t ht =>
      Subgroup.mem_centralizer_iff.mp hk t (hTB₀ ht)
  have h43'' := hL43 _ hFC''
  have hc6 := card_bstar_le_of_ggL43 hBs hxBs hx1 h43''
  have hc7 : p * Nat.card B₁ ≤ Nat.card Bs := by
    refine mul_card_le_card_of_lt (fun g hg => hBs.2 g hg)
      (lt_of_le_of_ne inf_le_left fun h => h43.1 ?_)
    have hx' : x ∈ B₁ := by rw [h]; exact hxBs
    exact hx'
  have hB₁'' : Bs ⊓ Subgroup.centralizer ((flagRadical Bs B₁ T : Subgroup G) : Set G) ≤ B₁ :=
    inf_le_inf_left _ (Subgroup.centralizer_le hXX)
  have hB₁eq : Bs ⊓ Subgroup.centralizer ((flagRadical Bs B₁ T : Subgroup G) : Set G) = B₁ :=
    Subgroup.eq_of_le_of_card_ge hB₁''
      (Nat.le_of_mul_le_mul_left (hc7.trans (hc6.trans (le_of_eq (mul_comm _ _)))) hp.pos)
  have haX : a ∈ Bs ⊓ Subgroup.centralizer ((flagRadical Bs B₁ T : Subgroup G) : Set G) := by
    rw [hB₁eq]
    exact ha
  have hka' : k * a = a * k := Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp haX).2 k hkX
  apply he1
  have h1 : k * a * k⁻¹ = a := by rw [hka', mul_inv_cancel_right]
  rw [hka] at h1
  exact mul_right_cancel (h1.trans (one_mul a).symm)

end FlagFinite

end GGL44CF

theorem ggL44iiiMcLaughlinInput_of_lang (hTB : GGTableBCxInput) (hNN : GGXNotNormalInput)
    (hTBM : GGTableBModuleInput) (hTBA : GGTableBActionInput) (hlang : GGNbrLangAxisInput) :
    GGL44iiiMcLaughlinInput := by
  intro G _ _ p B Bs x L D J X B₂ hFC hM h43 h44 _ h44b d _ _ y K hnbr _ hN P hP
  refine largeEvenMarking_mono ?_ (hlang G p B Bs x L D J hFC.1 y K hnbr hN P hP)
  rintro lab R _ I F θ ⟨hPθ, hQ⟩
  refine ⟨hPθ, fun hgr hT _ a ha => ?_⟩
  by_contra haI
  obtain ⟨B₀, hB₀, hcard, haB₀, hax, k, hk, e, he, he1, hka⟩ := hQ hgr a ha.1 haI
  exact GGL44CF.false_of_lang_axis (fun X' hX' => ggL43_noBL5 hTB hNN hTBM hTBA hX') hFC hM
    h43 h44 h44b ha hB₀ hcard haB₀ (fun b hb => hax b hb.1.1 (hT b hb)) hk he he1 hka

end CFSG.StandardType

end
