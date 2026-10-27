module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem25OddA
public import Certificates.Certificate3951
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
import CFSG.LocalAnalysis.EvenBN.TrialityD4.Native
import CFSG.LocalAnalysis.EvenBN.TrialityD4.Sylow
import CFSG.LocalAnalysis.EvenBN.TrialityD4.Bruhat
public import CFSG.Assembly.QuasithinDefs
public import CFSG.LieType.Chevalley.RootCommutatorData
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.Background.A3StructureFacts
public import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.ComplementTransfer
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import Certificates.Certificate43

public section

namespace CFSG.Quasithin.H13.OddSyl

open CFSG.QuasithinUnique CFSG.Quasithin

theorem mem_normalizer_of_conj_mem {G : Type} [Group G] [Finite G] {H : Subgroup G} {g : G}
    (h : ∀ x ∈ H, g * x * g⁻¹ ∈ H) : g ∈ Subgroup.normalizer (H : Set G) := by
  have hmap : H.map (MulAut.conj g).toMonoidHom = H := by
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rintro _ ⟨x, hx, rfl⟩
      exact h x hx
    · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨h x, fun hx => ?_⟩
  rw [← hmap] at hx
  obtain ⟨z, hz, hzx⟩ := hx
  have hzx' : g * z * g⁻¹ = g * x * g⁻¹ := hzx
  have hzeq : z = x := mul_left_cancel (mul_right_cancel hzx')
  exact hzeq ▸ hz

open CFSG.LocalAnalysis.EvenBN.TrialityD4
open scoped Pointwise

variable {X : Type} [Group X] {q : ℕ}

private theorem phi_mem_S (d : TrialityD4Data X q) {y : X} (hy : y ∈ d.S) : d.φ y ∈ d.S := by
  have hle : d.S.map d.φ.toMonoidHom ≤ d.S := by
    change (sixClosure d.x₁ d.x₂ d.x₃ d.x₄ d.x₅ d.x₆).map d.φ.toMonoidHom ≤ d.S
    rw [sixClosure, MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨z, hz, rfl⟩
    have hgen : ∀ w ∈ Set.range d.x₁ ∪ Set.range d.x₂ ∪ Set.range d.x₃ ∪ Set.range d.x₄ ∪
        Set.range d.x₅ ∪ Set.range d.x₆, w ∈ d.S := fun w hw => Subgroup.subset_closure hw
    rcases hz with (((((⟨a, rfl⟩ | ⟨a, rfl⟩) | ⟨a, rfl⟩) | ⟨a, rfl⟩) | ⟨a, rfl⟩) | ⟨a, rfl⟩)
    · change d.φ (d.x₁ a) ∈ d.S
      rw [d.φ_x₁]
      exact hgen _ (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl ⟨_, rfl⟩)))))
    · change d.φ (d.x₂ a) ∈ d.S
      rw [d.φ_x₂]
      exact hgen _ (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨_, rfl⟩)))))
    · change d.φ (d.x₃ a) ∈ d.S
      rw [d.φ_x₃]
      exact hgen _ (Or.inl (Or.inl (Or.inl (Or.inr ⟨_, rfl⟩))))
    · change d.φ (d.x₄ a) ∈ d.S
      rw [d.φ_x₄]
      exact hgen _ (Or.inl (Or.inl (Or.inr ⟨_, rfl⟩)))
    · change d.φ (d.x₅ a) ∈ d.S
      rw [d.φ_x₅]
      exact hgen _ (Or.inl (Or.inr ⟨_, rfl⟩))
    · change d.φ (d.x₆ a) ∈ d.S
      rw [d.φ_x₆]
      exact hgen _ (Or.inr ⟨_, rfl⟩)
  exact hle ⟨y, hy, rfl⟩

private theorem phi_pow_mem_S (d : TrialityD4Data X q) (k : ℕ) {y : X} (hy : y ∈ d.S) :
    (d.φ ^ k) y ∈ d.S := by
  induction k with
  | zero => simpa using hy
  | succ k ih =>
    rw [pow_succ', MulAut.mul_apply]
    exact phi_mem_S d ih

private theorem phi_pow_torus (d : TrialityD4Data X q) (k : ℕ) (h : (d.Γ₀)ˣ × d.Γˣ) :
    (d.φ ^ k) (d.torus h) = d.torus (h ^ 2 ^ k) := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ', MulAut.mul_apply, ih, d.φ_torus, ← pow_mul, ← pow_succ]

private theorem eq_seven_of_data [Finite X] (d : TrialityD4Data X q) (hq : q = 2)
    (hinj : Function.Injective (MulAut.conj : X →* MulAut X)) {α : MulAut X} {r : ℕ}
    (hr : r.Prime) (hr2 : r ≠ 2) (hα : orderOf α = r) (hαS : d.S.map α.toMonoidHom = d.S)
    (hcent : ∀ y ∈ Subgroup.normalizer (d.S : Set X), α y * y⁻¹ ∈ d.S) :
    r = 7 ∧ α ∈ innAut X := by
  subst hq
  have hJN : d.J ≤ Subgroup.normalizer (d.S : Set X) := by
    rw [d.normalizer_S]
    exact le_sup_right
  have hφ3 : orderOf d.φ = 3 := by
    have h := d.two_pow_orderOf_φ
    exact Nat.pow_right_injective le_rfl h
  obtain ⟨g, k, hgk⟩ := d.aut_eq α
  have hmod : d.φ ^ k = d.φ ^ (k % 3) := by
    rw [← hφ3, pow_mod_orderOf]
  rw [hmod] at hgk
  have hk3 : k % 3 < 3 := Nat.mod_lt _ (by norm_num)
  set m := k % 3 with hm
  rcases (by omega : m = 0 ∨ m = 1 ∨ m = 2) with hm0 | hm12
  ·
    rw [hm0, pow_zero, mul_one] at hgk
    have hinn : α ∈ innAut X := ⟨g, hgk.symm⟩
    refine ⟨?_, hinn⟩
    obtain ⟨g', hg'N, -, hg'o⟩ := exists_conj_of_mem_innAut hinj hα hαS hinn
    have hB : Nat.card (Subgroup.normalizer (d.S : Set X)) = 2 ^ 12 * 7 := by
      rw [d.normalizer_S, d.card_B, d.card_S, d.card_J]
      norm_num
    have hdvd : r ∣ 2 ^ 12 * 7 := by
      rw [← hB, ← hg'o]
      exact Subgroup.orderOf_dvd_natCard _ hg'N
    rcases (Nat.Prime.dvd_mul hr).1 hdvd with h | h
    · exact absurd ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 (hr.dvd_of_dvd_pow h)) hr2
    · exact (Nat.prime_dvd_prime_iff_eq hr (by norm_num)).1 h
  · exfalso
    have hφS : d.S.map (d.φ ^ m).toMonoidHom = d.S := by
      refine Subgroup.eq_of_le_of_card_ge ?_ ?_
      · rintro _ ⟨x, hx, rfl⟩
        exact phi_pow_mem_S d m hx
      · rw [Subgroup.card_map_of_injective (d.φ ^ m).injective]
    have hφS' : ∀ y ∈ d.S, (d.φ ^ m).symm y ∈ d.S := by
      intro y hy
      rw [← hφS] at hy
      obtain ⟨z, hz, rfl⟩ := hy
      change (d.φ ^ m).symm ((d.φ ^ m) z) ∈ d.S
      rw [MulEquiv.symm_apply_apply]
      exact hz
    have hαmem : ∀ y ∈ d.S, α y ∈ d.S := fun y hy => by
      rw [← hαS]
      exact ⟨y, hy, rfl⟩
    have hgN : g ∈ Subgroup.normalizer (d.S : Set X) := by
      refine mem_normalizer_of_conj_mem fun x hx => ?_
      have h1 : α ((d.φ ^ m).symm x) = g * x * g⁻¹ := by
        rw [hgk, MulAut.mul_apply, MulEquiv.apply_symm_apply, MulAut.conj_apply]
      rw [← h1]
      exact hαmem _ (hφS' x hx)
    have hgB : g ∈ (d.S : Set X) * (d.J : Set X) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left d.S d.J hJN]
      have h := hgN
      rw [d.normalizer_S] at h
      exact h
    obtain ⟨s, hs, j, hj, rfl⟩ := Set.mem_mul.mp hgB
    obtain ⟨hj', rfl⟩ := hj
    have hΓ : Nat.card d.Γˣ = 7 := by
      rw [d.card_units_Γ]
      norm_num
    have : Nontrivial d.Γˣ := Finite.one_lt_card_iff_nontrivial.mp (by rw [hΓ]; norm_num)
    obtain ⟨μ, hμ⟩ := exists_ne (1 : d.Γˣ)
    have hμ7 : μ ^ 7 = 1 := by
      rw [← hΓ]
      exact pow_card_eq_one'
    have hcomm : ∀ a b : (d.Γ₀)ˣ × d.Γˣ, d.torus a * d.torus b = d.torus b * d.torus a := by
      intro a b
      rw [← map_mul, ← map_mul, mul_comm]
    have hyN : d.torus (1, μ) ∈ Subgroup.normalizer (d.S : Set X) := hJN ⟨(1, μ), rfl⟩
    have hc := hcent _ hyN
    have hαy : α (d.torus (1, μ)) = s * d.torus ((1, μ) ^ 2 ^ m) * s⁻¹ := by
      rw [hgk, MulAut.mul_apply, phi_pow_torus, MulAut.conj_apply]
      have htx := hcomm hj' ((1, μ) ^ 2 ^ m)
      calc s * d.torus hj' * d.torus ((1, μ) ^ 2 ^ m) * (s * d.torus hj')⁻¹ =
            s * (d.torus hj' * d.torus ((1, μ) ^ 2 ^ m)) * (d.torus hj')⁻¹ * s⁻¹ := by group
        _ = s * (d.torus ((1, μ) ^ 2 ^ m) * d.torus hj') * (d.torus hj')⁻¹ * s⁻¹ := by
            rw [htx]
        _ = s * d.torus ((1, μ) ^ 2 ^ m) * s⁻¹ := by group
    rw [hαy] at hc
    have hysy : d.torus (1, μ) * s * (d.torus (1, μ))⁻¹ ∈ d.S :=
      (Subgroup.mem_normalizer_iff.mp hyN s).mp hs
    have hxy : d.torus ((1, μ) ^ 2 ^ m) * (d.torus (1, μ))⁻¹ ∈ d.S := by
      have h := d.S.mul_mem (d.S.mul_mem (d.S.inv_mem hs) hc) hysy
      have heq : s⁻¹ * (s * d.torus ((1, μ) ^ 2 ^ m) * s⁻¹ * (d.torus (1, μ))⁻¹) *
          (d.torus (1, μ) * s * (d.torus (1, μ))⁻¹) =
          d.torus ((1, μ) ^ 2 ^ m) * (d.torus (1, μ))⁻¹ := by group
      rwa [heq] at h
    have hxyJ : d.torus ((1, μ) ^ 2 ^ m) * (d.torus (1, μ))⁻¹ ∈ d.J :=
      ⟨(1, μ) ^ 2 ^ m * (1, μ)⁻¹, by rw [map_mul, map_inv]⟩
    have hxy1 : d.torus ((1, μ) ^ 2 ^ m) * (d.torus (1, μ))⁻¹ = 1 := by
      have h : d.torus ((1, μ) ^ 2 ^ m) * (d.torus (1, μ))⁻¹ ∈ d.S ⊓ d.J :=
        Subgroup.mem_inf.mpr ⟨hxy, hxyJ⟩
      rw [d.S_inf_J, Subgroup.mem_bot] at h
      exact h
    have hxyeq : (1, μ) ^ 2 ^ m = ((1, μ) : (d.Γ₀)ˣ × d.Γˣ) :=
      d.torus_injective (mul_inv_eq_one.mp hxy1)
    have hμm : μ ^ 2 ^ m = μ := by
      have h := congrArg Prod.snd hxyeq
      simpa using h
    rcases hm12 with hm1 | hm2
    · rw [hm1, pow_one, pow_two] at hμm
      exact hμ (mul_left_cancel (a := μ) (by rw [mul_one]; exact hμm))
    · rw [hm2] at hμm
      have h4 : μ ^ 4 = μ ^ 3 * μ := pow_succ μ 3
      have hμ4 : μ ^ 4 = μ := by simpa using hμm
      have h3 : μ ^ 3 = 1 := by
        rw [h4] at hμ4
        exact mul_right_cancel (b := μ) (by rw [one_mul]; exact hμ4)
      have h1 : orderOf μ ∣ Nat.gcd 3 7 :=
        Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h3) (orderOf_dvd_of_pow_eq_one hμ7)
      rw [show Nat.gcd 3 7 = 1 by norm_num, Nat.dvd_one, orderOf_eq_one_iff] at h1
      exact hμ h1

theorem oddSylowD42_holds :
    OddSylowD42 := by
  intro S _ _ hS hna hm P hP α r hr hr2 hα hαP _ hcent
  have hlie : CFSG.Blueprint.LieModel S .trialityD4 0 2 1 :=
    Or.inr (Or.inl ⟨rfl, by decide, hm⟩)
  obtain ⟨d⟩ := nonempty_trialityD4Data_of_lieModel le_rfl hlie
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hQ⟩ := d.exists_sylow_eq_S
  have hidx : ¬ 2 ∣ P.index := by
    rw [← Subgroup.relIndex_top_right]
    exact hP.2.2
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq S Q (hP.2.1.toSylow hidx)
  have hd'S : (d.ofMulEquiv (MulAut.conj c)).S = P := by
    have h1 : (d.ofMulEquiv (MulAut.conj c)).S = d.S.map (MulAut.conj c).toMonoidHom :=
      d.sixClosure_map (MulAut.conj c)
    ext y
    rw [h1, Subgroup.mem_map_equiv, MulAut.conj_symm_apply, ← hQ]
    have h2 : y ∈ ((c • Q : Sylow 2 S) : Subgroup S) ↔ y ∈ P := by
      rw [hc]
      exact Iff.rfl
    rw [← h2, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
      MulAut.smul_def, MulAut.conj_inv_apply]
  subst hd'S
  exact eq_seven_of_data _ (by norm_num) (conj_injective hS hna) hr hr2 hα hαP hcent

end CFSG.Quasithin.H13.OddSyl
