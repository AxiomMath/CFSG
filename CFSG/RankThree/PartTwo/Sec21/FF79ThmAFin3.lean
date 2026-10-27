module

public import CFSG.RankThree.PartTwo.Sec21.FF79ThmAFin2
public import CFSG.RankThree.PartTwo.Sec21.FF79ThmAAct2
import CFSG.LieType.Simplicity.Classical

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79

open CFSG CFSG.RankThree.PartTwo.Sec21
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)

variable {G : Type} [Group G]

theorem mem_OUpp_of_pow {p k : ℕ} {H : Subgroup G} {x : G} (hx : x ∈ H) (h : x ^ (p ^ k) = 1) :
    x ∈ OUpp p H :=
  ⟨⟨x, hx⟩, Subgroup.subset_normalClosure ⟨k, Subtype.ext (by simpa using h)⟩, rfl⟩

variable [Finite G]

theorem sq_centralizes (hb34 : FF79KL34b) {b p : G} {U₁ U₂ : Subgroup G}
    (hU₂ : Nat.card U₂ = 9) (hU₂L : U₂ ≤ OppE 3 (CenS U₁))
    (hmodel : StatedClassicalModel (LayerQ (CenS U₁)) .PSL 3 2 2)
    (hK : StatedClassicalModel (OUpp 2 (OppE 3 (CenS U₁) ⊓ Cen b)) .PSL 2 2 2)
    (hpU₁ : p ∈ Nor U₁) (hpU₂ : p ∈ CenS U₂) (hp4 : p ^ 4 = 1) (hpb : b * p ^ 2 * b⁻¹ = p ^ 2) :
    ∀ k ∈ OUpp 2 (OppE 3 (CenS U₁) ⊓ Cen b), p ^ 2 * k = k * p ^ 2 := by
  set N := CenS U₁ with hN
  have hpN : p ∈ Nor N := nor_cenS_of_nor hpU₁
  have hact := actE_sq_eq_one hb34 hU₂ hU₂L hmodel hpN (fun u hu => by
    have := Subgroup.mem_centralizer_iff.mp hpU₂ u hu
    rw [← this]; group) hp4
  have hζN : p ^ 2 ∈ Nor N := Subgroup.pow_mem _ hpN 2
  have hζL : p ^ 2 ∈ Nor (OppE 3 N) := nor_OppE_of_nor hζN
  have hζc : p ^ 2 ∈ Cen b := by
    refine Subgroup.mem_centralizer_iff.mpr fun h hh => ?_
    rw [Set.mem_singleton_iff.mp hh]
    exact mul_inv_eq_iff_eq_mul.mp hpb
  have hζK : ∀ x ∈ OUpp 2 (OppE 3 N ⊓ Cen b), p ^ 2 * x * (p ^ 2)⁻¹ ∈ OUpp 2 (OppE 3 N ⊓ Cen b) :=
    fun x hx => OUpp_conj_mem 2 (nor_inf hζL (mem_nor_self hζc)) hx
  intro k hk
  have hkL : k ∈ OppE 3 N := (OUpp_le 2 _ hk).1
  have hmem : p ^ 2 * k * (p ^ 2)⁻¹ ∈ OppE 3 N := (Subgroup.mem_normalizer_iff.mp hζL k).mp hkL
  have h1 := actE_Lπ N ⟨p ^ 2, hζN⟩ ⟨k, hkL⟩ ⟨_, hmem⟩ rfl
  rw [hact] at h1
  have h2 : Lπ N ⟨p ^ 2 * k * (p ^ 2)⁻¹ * k⁻¹, (OppE 3 N).mul_mem hmem ((OppE 3 N).inv_mem hkL)⟩
      = 1 := by
    have : (⟨p ^ 2 * k * (p ^ 2)⁻¹ * k⁻¹, (OppE 3 N).mul_mem hmem ((OppE 3 N).inv_mem hkL)⟩ :
        ↥(OppE 3 N)) = ⟨_, hmem⟩ * (⟨k, hkL⟩ : ↥(OppE 3 N))⁻¹ := rfl
    rw [this, map_mul, map_inv, ← h1]
    simp
  have h3 := (Lπ_eq_one_iff N _).mp h2
  have hKN : OUpp 2 (OppE 3 N ⊓ Cen b) ≤ N := (OUpp_le 2 _).trans (inf_le_left.trans (OppE_le N))
  have h4 : p ^ 2 * k * (p ^ 2)⁻¹ * k⁻¹ ∈ OUpp 2 (OppE 3 N ⊓ Cen b) ⊓ Opp 3 N :=
    ⟨Subgroup.mul_mem _ (hζK k hk) (Subgroup.inv_mem _ hk), h3⟩
  rw [inf_opp_eq_bot_of_l24 hKN hK] at h4
  have h5 : p ^ 2 * k * (p ^ 2)⁻¹ * k⁻¹ = 1 := h4
  calc p ^ 2 * k = (p ^ 2 * k * (p ^ 2)⁻¹ * k⁻¹) * k * p ^ 2 := by group
    _ = k * p ^ 2 := by rw [h5]; simp

theorem false_of_commuting_involution (hNo : FF79KNoInvA5) {n : ℕ} (hn : n = 4 ∨ n = 5)
    {J K : Subgroup G} (hJ : IsTypeLnq n 2 1 J) (hKJ : K ≤ J)
    (hK : StatedClassicalModel K .PSL 2 2 2)
    (hnz : ∀ t ∈ J, orderOf t = 2 → ¬ ∀ j ∈ J, t * j = j * t) {ζ : G} (hζJ : ζ ∈ J)
    (hζ : orderOf ζ = 2) (hζK : ∀ k ∈ K, ζ * k = k * ζ) : False := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : IsSimpleGroup K := (CFSG.LieType.Simplicity.fam_PSL_simplicity K 2 2 2 hK).2
  let φ : ↥(K.subgroupOf J) →* ↥J ⧸ Subgroup.center ↥J :=
    (QuotientGroup.mk' (Subgroup.center ↥J)).comp (K.subgroupOf J).subtype
  let e : ↥(K.subgroupOf J) ≃* K := Subgroup.subgroupOfEquivOfLe hKJ
  haveI : IsSimpleGroup ↥(K.subgroupOf J) := e.isSimpleGroup
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal φ.ker with h | h
    · intro x hx
      have : x ∈ φ.ker := hx
      rw [h] at this
      simpa using this
    · exfalso
      have h60 := l24_card_eq K hK
      haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      obtain ⟨k0, hk0⟩ := exists_prime_orderOf_dvd_card' (G := K) 2 (by rw [h60]; norm_num)
      have hk0J : (k0 : G) ∈ J := hKJ k0.2
      have hk0ord : orderOf (k0 : G) = 2 := by rw [Subgroup.orderOf_coe]; exact hk0
      refine hnz _ hk0J hk0ord fun j hj => ?_
      have hm : (e.symm k0) ∈ φ.ker := by rw [h]; trivial
      have hm' : (QuotientGroup.mk (⟨k0, hKJ k0.2⟩ : ↥J) : ↥J ⧸ Subgroup.center ↥J) = 1 := hm
      have hc := (QuotientGroup.eq_one_iff _).mp hm'
      have := Subgroup.mem_center_iff.mp hc ⟨j, hj⟩
      exact (congrArg Subtype.val this).symm
  have hKmodel : StatedClassicalModel φ.range .PSL 2 2 2 :=
    model_of_mulEquiv ((MonoidHom.ofInjective hinj).symm.trans e) hK
  have hζnc : ¬ ∀ j ∈ J, ζ * j = j * ζ := hnz ζ hζJ hζ
  have hq1 : (QuotientGroup.mk (⟨ζ, hζJ⟩ : ↥J) : ↥J ⧸ Subgroup.center ↥J) ≠ 1 := by
    intro h
    apply hζnc
    intro j hj
    have hc := (QuotientGroup.eq_one_iff _).mp h
    have := Subgroup.mem_center_iff.mp hc ⟨j, hj⟩
    exact (congrArg Subtype.val this).symm
  have hq2 : (QuotientGroup.mk (⟨ζ, hζJ⟩ : ↥J) : ↥J ⧸ Subgroup.center ↥J) ^ 2 = 1 := by
    rw [← QuotientGroup.mk_pow]
    have : (⟨ζ, hζJ⟩ : ↥J) ^ 2 = 1 := Subtype.ext (by
      have := pow_orderOf_eq_one ζ
      rw [hζ] at this
      simpa using this)
    rw [this]; rfl
  have hord := orderOf_eq_prime hq2 hq1
  refine hNo (↥J ⧸ Subgroup.center ↥J) n hn hJ φ.range hKmodel _ hord ?_
  rintro _ ⟨x, rfl⟩
  refine Subgroup.mem_centralizer_iff.mpr fun h hh => ?_
  rw [Set.mem_singleton_iff.mp hh]
  show (QuotientGroup.mk (⟨ζ, hζJ⟩ : ↥J) : ↥J ⧸ Subgroup.center ↥J) * φ x = φ x * _
  rw [show φ x = QuotientGroup.mk (x : ↥J) from rfl, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
  congr 1
  exact Subtype.ext (hζK x x.2)

end CFSG.RankThree.PartTwo.Sec21.FF79
