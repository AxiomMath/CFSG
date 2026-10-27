module

public import CFSG.LocalAnalysis.StandardType.GGQ2PrimeRhoTKer
public import CFSG.LocalAnalysis.StandardType.GGQ2PrimeRhoTLiftComm
public import CFSG.LocalAnalysis.StandardType.GGQ2PrimeF4CubeScalar
public import CFSG.LocalAnalysis.StandardType.GGQ2PrimeRhoTFrameKer
public import CFSG.LocalAnalysis.StandardType.GGQ2PrimeRhoTInner

public section

namespace CFSG.GGQ2Prime

open Subgroup CFSG.Open CFSG.Models CFSG.Assembly CFSG.StandardType CFSG.Fischer

theorem rhoTFrame_exists_E
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L : Subgroup G} {A : Subgroup (MulAut Bs)} {κ : Fin 7 → (Bs →* Multiplicative (ZMod 3))}
    {m : Fin 7} (h : CoordCtx B Bs x L A κ m) {e : (L ⧸ center L) ≃* T46}
    {ρ : normalizer (L : Set G) →* Equiv.Perm (Fin 693)} (hρ : RhoTSpec e ρ) :
    ∃ E : Subgroup (GL (Fin 6) F4), E ≤ SU0 ∧ (∀ a ∈ E, ∀ a' ∈ E, a * a' = a' * a) ∧
      (∀ a ∈ E, a ^ 3 = 1) ∧ 3 ^ 5 ≤ Nat.card E ∧
      ∀ a : SU0, (a : GL (Fin 6) F4) ∈ E ↔
        ∃ (b : G) (hb : b ∈ Bs), κ m ⟨b, hb⟩ = 1 ∧ piSU a = ρ ⟨b, h.setting.Bs_norm hb⟩ := by
  classical
  obtain ⟨-, hBab, -, -⟩ := h.setting.bstar
  have hBs3 : ∀ b ∈ Bs, b ^ 3 = 1 := hBab.2
  let ρB : Bs →* Equiv.Perm (Fin 693) := ρ.comp (Subgroup.inclusion h.setting.Bs_norm)
  let Kb : Subgroup Bs := (κ m).ker
  let Hρ : Subgroup (Equiv.Perm (Fin 693)) := Kb.map ρB
  have hKb : ∀ b : Bs, b ∈ Kb ↔ κ m b = 1 := fun b => MonoidHom.mem_ker
  have hHT : Hρ ≤ T46 := by
    rintro _ ⟨b, hb, rfl⟩
    exact (rhoT_mem_T46_iff h hρ b.2).2 ((hKb b).1 hb)
  have hKcard : 243 ≤ Nat.card Kb := by
    have h1 : Nat.card Kb * Kb.index = Nat.card Bs := Subgroup.card_mul_index Kb
    have h2 : Kb.index ≤ 3 := by
      show (κ m).ker.index ≤ 3
      rw [Subgroup.index_ker]
      calc Nat.card (κ m).range ≤ Nat.card (Multiplicative (ZMod 3)) :=
            Subgroup.card_le_card_group _
        _ = 3 := by simp
    have h3 := Nat.mul_le_mul_left (Nat.card Kb) h2
    rw [h.setting.Bs_card] at h1
    omega
  have hker : Nat.card (ρB.domRestrict Kb).ker ≤ 3 := by
    let x₀ : Bs := ⟨x, h.coords.x_mem⟩
    have hx0 : x₀ ^ 3 = 1 := Subtype.ext (by simpa using hBs3 x h.coords.x_mem)
    have hz3 : Nat.card (zpowers x₀) ≤ 3 := by
      rw [Nat.card_zpowers]
      exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one hx0)
    have hmem : ∀ k : (ρB.domRestrict Kb).ker, ((k : Kb) : Bs) ∈ zpowers x₀ := by
      intro k
      have h1 : ρ ⟨(((k : Kb) : Bs) : G), h.setting.Bs_norm ((k : Kb) : Bs).2⟩ = 1 :=
        MonoidHom.mem_ker.1 k.2
      obtain ⟨t, ht⟩ := Subgroup.mem_zpowers_iff.1
        ((rhoT_eq_one_iff_mem_zpowers h hρ ((k : Kb) : Bs).2).1 h1)
      exact ⟨t, Subtype.ext (by simpa using ht)⟩
    have hf : Function.Injective fun k : (ρB.domRestrict Kb).ker =>
        (⟨((k : Kb) : Bs), hmem k⟩ : zpowers x₀) := fun k k' hkk' =>
      Subtype.ext (Subtype.ext (congrArg (fun z : zpowers x₀ => ((z : Bs))) hkk'))
    exact (Nat.card_le_card_of_injective _ hf).trans hz3
  have hHcard : 81 ≤ Nat.card Hρ := by
    have h1 := Subgroup.card_ker_mul_card_range (ρB.domRestrict Kb)
    have hr : (ρB.domRestrict Kb).range = Hρ := MonoidHom.domRestrict_range Kb ρB
    rw [hr] at h1
    have := Nat.mul_le_mul_right (Nat.card Hρ) hker
    omega
  let Et : Subgroup SU0 := Hρ.comap piSU
  have hcardEt : 243 ≤ Nat.card Et := by
    have hker_le : piSU.ker ≤ Et := Subgroup.ker_le_comap piSU Hρ
    have h1 := Subgroup.card_ker_mul_card_range (piSU.domRestrict Et)
    have hrange : (piSU.domRestrict Et).range = Hρ := by
      rw [MonoidHom.domRestrict_range]
      exact Subgroup.map_comap_eq_self (by rw [range_piSU]; exact hHT)
    have hkercard : Nat.card (piSU.domRestrict Et).ker = Nat.card piSU.ker := by
      rw [MonoidHom.ker_domRestrict]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hker_le).toEquiv
    have h3 : 3 ≤ Nat.card piSU.ker :=
      three_le_card_center.trans (Subgroup.card_le_of_le center_le_ker)
    rw [hrange, hkercard] at h1
    have := Nat.mul_le_mul_right (Nat.card Hρ) h3
    omega
  let E : Subgroup (GL (Fin 6) F4) := Et.map SU0.subtype
  have hmemE : ∀ a : SU0, (a : GL (Fin 6) F4) ∈ E ↔ piSU a ∈ Hρ := by
    intro a
    constructor
    · rintro ⟨a', ha', hae⟩
      have : a' = a := Subtype.ext hae
      rw [← this]
      exact ha'
    · intro ha
      exact ⟨a, ha, rfl⟩
  have hcube : ∀ a₀ : SU0, piSU a₀ ∈ Hρ → a₀ ^ 3 = 1 := by
    intro a₀ ha₀
    obtain ⟨b', -, hbρ⟩ := ha₀
    have h1 : piSU (a₀ ^ 3) = 1 := by
      rw [map_pow, ← hbρ, ← map_pow]
      have : b' ^ 3 = 1 := Subtype.ext (by simpa using hBs3 b' b'.2)
      rw [this, map_one]
    obtain ⟨c, -, hc⟩ := rhoTFrame_ker_scalar h1
    have hdet : ((a₀ : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4).det = 1 := by
      rw [← Matrix.GeneralLinearGroup.val_det_apply, (mem_SU0.1 a₀.2).1]
      rfl
    have hpow : ((a₀ : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) ^ 3 =
        Matrix.scalar (Fin 6) c := by
      have e3 : ((a₀ ^ 3 : SU0) : GL (Fin 6) F4) = (a₀ : GL (Fin 6) F4) ^ 3 := rfl
      rw [e3, Units.val_pow_eq_pow_val] at hc
      rw [hc, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
    have hc1 : c = 1 := eq_one_of_det_eq_one_of_pow_three_eq_scalar hdet hpow
    apply Subtype.ext
    apply Units.ext
    rw [hc, hc1, one_smul]
    rfl
  have hex : ∀ a : SU0, piSU a ∈ Hρ ↔
      ∃ (b : G) (hb : b ∈ Bs), κ m ⟨b, hb⟩ = 1 ∧ piSU a = ρ ⟨b, h.setting.Bs_norm hb⟩ := by
    intro a
    constructor
    · rintro ⟨b', hb', hbρ⟩
      exact ⟨b', b'.2, (hKb b').1 hb', hbρ.symm⟩
    · rintro ⟨b, hb, hκ, hpi⟩
      exact ⟨⟨b, hb⟩, (hKb ⟨b, hb⟩).2 hκ, hpi.symm⟩
  refine ⟨E, Subgroup.map_subtype_le Et, ?_, ?_, ?_, fun a => (hmemE a).trans (hex a)⟩
  · rintro _ ⟨a₁, ha₁, rfl⟩ _ ⟨a₂, ha₂, rfl⟩
    obtain ⟨b₁, hb₁, hρ₁⟩ := ha₁
    obtain ⟨b₂, hb₂, hρ₂⟩ := ha₂
    have hKB : Kb.map Bs.subtype ≤ Bs := Subgroup.map_subtype_le Kb
    have key := rhoT_lift_commute h hρ (K := Kb.map Bs.subtype) hKB
      (fun b hb hκ => ⟨⟨b, hb⟩, (hKb ⟨b, hb⟩).2 hκ, rfl⟩)
      (fun b hb => by
        obtain ⟨b', hb', rfl⟩ := hb
        exact (rhoT_mem_T46_iff h hρ b'.2).2 ((hKb b').1 hb'))
      (a := a₁) (a' := a₂) (b := (b₁ : G)) (b' := (b₂ : G)) ⟨b₁, hb₁, rfl⟩ ⟨b₂, hb₂, rfl⟩
      hρ₁.symm hρ₂.symm
    exact congrArg Subtype.val key
  · rintro _ ⟨a₁, ha₁, rfl⟩
    exact congrArg Subtype.val (hcube a₁ ha₁)
  · have h5 : (3 : ℕ) ^ 5 = 243 := by norm_num
    rw [h5, Subgroup.card_subtype SU0 Et]
    exact hcardEt

end CFSG.GGQ2Prime
