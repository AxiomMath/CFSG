module

public import CFSG.Quasithin.H13.A6S13821zd
public import CFSG.Quasithin.H13.A6S13821v
public import CFSG.CharacterTheory.Semidihedral.Principal.FreeSixCharacterDefectFourSupport

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.Quasithin.E1.LiftS5

attribute [local instance] commGroupOfFact

namespace A6L24

variable {W : Type*} [CommGroup W]

theorem pow_twelve_of_transv (hW : ∀ w : W, w ^ 2 = 1) {t₁ t₂ : MulAut W} {w₁ w₂ : W}
    (h₁ : ∀ v, t₁ v = v ∨ t₁ v = v * w₁) (h₂ : ∀ v, t₂ v = v ∨ t₂ v = v * w₂) :
    (t₁ * t₂) ^ 12 = 1 := by
  set C := Subgroup.closure ({w₁, w₂} : Set W) with hC
  have hw₁C : w₁ ∈ C := Subgroup.subset_closure (by simp)
  have hw₂C : w₂ ∈ C := Subgroup.subset_closure (by simp)
  have e₁ : w₁ * w₁ = 1 := by rw [← sq]; exact hW w₁
  have e₂ : w₂ * w₂ = 1 := by rw [← sq]; exact hW w₂
  have hd₁ : ∀ v, t₁ v * v⁻¹ ∈ C := fun v => by
    rcases h₁ v with h | h <;> rw [h]
    · rw [mul_inv_cancel]; exact C.one_mem
    · rw [mul_comm v w₁, mul_inv_cancel_right]; exact hw₁C
  have hd₂ : ∀ v, t₂ v * v⁻¹ ∈ C := fun v => by
    rcases h₂ v with h | h <;> rw [h]
    · rw [mul_inv_cancel]; exact C.one_mem
    · rw [mul_comm v w₂, mul_inv_cancel_right]; exact hw₂C
  set g := t₁ * t₂ with hg
  have hgv : ∀ v, g v = t₁ (t₂ v) := fun v => rfl
  have hd : ∀ v, g v * v⁻¹ ∈ C := fun v => by
    have e : g v * v⁻¹ = (t₁ (t₂ v) * (t₂ v)⁻¹) * (t₂ v * v⁻¹) := by rw [hgv]; group
    rw [e]
    exact C.mul_mem (hd₁ _) (hd₂ v)
  have hdk : ∀ k : ℕ, ∀ v, (g ^ k) v * v⁻¹ ∈ C := by
    intro k
    induction k with
    | zero => intro v; simp
    | succ k ih =>
      intro v
      have e : (g ^ (k + 1)) v * v⁻¹ =
          (g ((g ^ k) v) * ((g ^ k) v)⁻¹) * ((g ^ k) v * v⁻¹) := by
        rw [pow_succ', MulAut.mul_apply]
        group
      rw [e]
      exact C.mul_mem (hd _) (ih v)
  have hf₁ : t₁ w₁ = w₁ := by
    rcases h₁ w₁ with h | h
    · exact h
    · rw [e₁] at h
      have h1 : w₁ = 1 := t₁.injective (by rw [h, map_one])
      rw [h1, map_one]
  have hf₂ : t₂ w₂ = w₂ := by
    rcases h₂ w₂ with h | h
    · exact h
    · rw [e₂] at h
      have h1 : w₂ = 1 := t₂.injective (by rw [h, map_one])
      rw [h1, map_one]
  have fixp : ∀ (h : MulAut W) (w : W), h w = w → ∀ n : ℕ, (h ^ n) w = w := by
    intro h w hw n
    induction n with
    | zero => rfl
    | succ n ih => rw [pow_succ', MulAut.mul_apply, ih, hw]
  have hp2 : ∀ v, (g ^ 2) v = g (g v) := fun v => by rw [sq]; rfl
  have hp3 : ∀ v, (g ^ 3) v = g (g (g v)) := fun v => by
    rw [show (3 : ℕ) = 2 + 1 by rfl, pow_succ', MulAut.mul_apply, hp2]
  have hfix : (g ^ 6) w₁ = w₁ ∧ (g ^ 6) w₂ = w₂ := by
    rcases h₁ w₂ with ha | ha <;> rcases h₂ w₁ with hb | hb
    · have hg1 : g w₁ = w₁ := by rw [hgv, hb, hf₁]
      have hg2 : g w₂ = w₂ := by rw [hgv, hf₂, ha]
      exact ⟨fixp g w₁ hg1 6, fixp g w₂ hg2 6⟩
    · have hg1 : g w₁ = w₁ * w₂ := by rw [hgv, hb, map_mul, hf₁, ha]
      have hg2 : g w₂ = w₂ := by rw [hgv, hf₂, ha]
      have h21 : (g ^ 2) w₁ = w₁ := by
        rw [hp2, hg1, map_mul, hg1, hg2, mul_assoc, e₂, mul_one]
      have h22 : (g ^ 2) w₂ = w₂ := by rw [hp2, hg2, hg2]
      rw [show (6 : ℕ) = 2 * 3 by rfl, pow_mul]
      exact ⟨fixp _ w₁ h21 3, fixp _ w₂ h22 3⟩
    · have hg1 : g w₁ = w₁ := by rw [hgv, hb, hf₁]
      have hg2 : g w₂ = w₂ * w₁ := by rw [hgv, hf₂, ha]
      have h21 : (g ^ 2) w₁ = w₁ := by rw [hp2, hg1, hg1]
      have h22 : (g ^ 2) w₂ = w₂ := by
        rw [hp2, hg2, map_mul, hg2, hg1, mul_assoc, e₁, mul_one]
      rw [show (6 : ℕ) = 2 * 3 by rfl, pow_mul]
      exact ⟨fixp _ w₁ h21 3, fixp _ w₂ h22 3⟩
    · have hg1 : g w₁ = w₂ := by
        rw [hgv, hb, map_mul, hf₁, ha, mul_comm w₂ w₁, ← mul_assoc, e₁, one_mul]
      have hg2 : g w₂ = w₂ * w₁ := by rw [hgv, hf₂, ha]
      have hg3 : g (w₂ * w₁) = w₁ := by
        rw [map_mul, hg2, hg1, mul_comm w₂ w₁, mul_assoc, e₂, mul_one]
      have h31 : (g ^ 3) w₁ = w₁ := by rw [hp3, hg1, hg2, hg3]
      have h32 : (g ^ 3) w₂ = w₂ := by rw [hp3, hg2, hg3, hg1]
      rw [show (6 : ℕ) = 3 * 2 by rfl, pow_mul]
      exact ⟨fixp _ w₁ h31 2, fixp _ w₂ h32 2⟩
  have hfC : ∀ d ∈ C, (g ^ 6) d = d := by
    intro d hd
    rw [hC] at hd
    induction hd using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with rfl | rfl
      · exact hfix.1
      · exact hfix.2
    | one => exact map_one _
    | mul x y _ _ hx hy => rw [map_mul, hx, hy]
    | inv x _ hx => rw [map_inv, hx]
  have hsq : ∀ v, (g ^ 6) ((g ^ 6) v) = v := by
    intro v
    set δ := (g ^ 6) v * v⁻¹ with hδ
    have hδC : δ ∈ C := hdk 6 v
    have hv : (g ^ 6) v = δ * v := by rw [hδ, inv_mul_cancel_right]
    rw [hv, map_mul, hfC δ hδC, hv, ← mul_assoc, ← sq, hW, one_mul]
  refine MulEquiv.ext fun v => ?_
  rw [show (12 : ℕ) = 6 + 6 by rfl, pow_add, MulAut.mul_apply, hsq, MulAut.one_apply]

end A6L24

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting4 G T L V)
include S

theorem isV4_of_mem_R1_l24 (hhat : ¬ IsHatA6 L)
    {H K : Subgroup G} (hLTH : S.L1 ⊔ T ≤ H) (hL1K : S.L1 ≤ K)
    (hKn : H ≤ Subgroup.normalizer (K : Set G))
    (e : ↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 5)) {p₀ : Fin 5}
    (hfix : ∀ g : ↥H, (g : G) ∈ S.L1 ⊔ T → quotPerm hKn e g p₀ = p₀) {r : G}
    (hr : r ∈ pCoreOf 2 (S.L1 ⊔ T)) :
    A6L24.IsV4 p₀ (quotPerm hKn e ⟨r, hLTH (pCoreOf_le 2 _ hr)⟩) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set R := pCoreOf 2 (S.L1 ⊔ T) with hR
  set c : G := (S.cL1 hhat : G) with hc
  have hcL1 : c ∈ S.L1 := S.cL1_mem hhat
  have hcLT : c ∈ S.L1 ⊔ T := Subgroup.mem_sup_left hcL1
  have hcH : c ∈ H := hLTH hcLT
  have hc3 : c ^ 3 = 1 := S.cL1_cube hhat
  have hcp : quotPerm hKn e ⟨c, hcH⟩ p₀ = p₀ := hfix _ hcLT
  have hψc3 : quotPerm hKn e ⟨c, hcH⟩ ^ 3 = 1 := by
    have h1 : (⟨c, hcH⟩ : ↥H) ^ 3 = 1 := Subtype.ext (by simpa using hc3)
    rw [← map_pow, h1, map_one]
  have hψc1 : quotPerm hKn e ⟨c, hcH⟩ ≠ 1 := by
    intro h1
    have h2 := (A6L24.quotPerm_eq_one_iff_of_mem hKn e _ (hL1K hcL1)).mp h1
    obtain ⟨k, hk⟩ := pCoreOf_isPGroup 2 K ⟨c, h2⟩
    have hk' : c ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have h3 : orderOf c ∣ Nat.gcd 3 (2 ^ k) :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hc3) (orderOf_dvd_of_pow_eq_one hk')
    have h4 : Nat.gcd 3 (2 ^ k) = 1 := Nat.Coprime.pow_right _ (by decide : Nat.Coprime 3 2)
    rw [h4, Nat.dvd_one, orderOf_eq_one_iff] at h3
    exact S.cL1_not_mem hhat
      (show c ∈ pCoreOf 2 S.L1 by rw [h3]; exact (pCoreOf 2 S.L1).one_mem)
  have h4 : ∀ g : ↥H, (g : G) ∈ R → quotPerm hKn e g ^ 4 = 1 := by
    intro g hg
    obtain ⟨k, hk⟩ := pCoreOf_isPGroup 2 (S.L1 ⊔ T) ⟨_, hg⟩
    exact A6L24.pow_four_eq_one hKn e (k := k) (by simpa using congrArg Subtype.val hk)
  have hRn : ∀ x ∈ R, c * x * c⁻¹ ∈ R ∧ c⁻¹ * x * c ∈ R := by
    intro x hx
    refine ⟨(Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 (S.L1 ⊔ T) hcLT) x).mp hx,
      ?_⟩
    have h1 := (Subgroup.mem_normalizer_iff.mp
      (le_normalizer_pCoreOf 2 (S.L1 ⊔ T) ((S.L1 ⊔ T).inv_mem hcLT)) x).mp hx
    simpa using h1
  set rr : ↥H := ⟨r, hLTH (pCoreOf_le 2 _ hr)⟩ with hrr
  set cc : ↥H := ⟨c, hcH⟩ with hcc
  have hA := h4 (rr * (cc * rr * cc⁻¹)) (R.mul_mem hr (hRn r hr).1)
  have hB := h4 (rr * (cc⁻¹ * rr * cc)) (R.mul_mem hr (hRn r hr).2)
  have hC := h4 ((cc * rr * cc⁻¹) * (cc⁻¹ * rr * cc)) (R.mul_mem (hRn r hr).1 (hRn r hr).2)
  simp only [map_mul, map_inv] at hA hB hC
  exact A6L24.isV4_of_normal p₀ _ ⟨hcp, hψc3, hψc1⟩ _
    ⟨hfix rr (pCoreOf_le 2 _ hr), h4 rr hr, hA, hB, hC⟩

theorem mem_QH_of_quotPerm_eq_one {H : Subgroup G} (hH : H ∈ S.Hz) {K : Subgroup G}
    (hKn : H ≤ Subgroup.normalizer (K : Set G)) (hHT : H = K ⊔ T)
    (e : ↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 5)) (g : ↥H)
    (hg : quotPerm hKn e g = 1) : (g : G) ∈ pCoreOf 2 H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTH : T ≤ H := le_sup_right.trans hH.1.1
  have hT2 : IsPGroup 2 T := (isSylowTwoOf_of_quasithinIsSylowTwo S.h13.sylow hTH).2.1
  have hTN : T ≤ Subgroup.normalizer (K : Set G) := hTH.trans hKn
  have hp : IsPGroup 2 (quotPerm hKn e).ker := by
    intro y
    obtain ⟨a, ha⟩ := E1.exists_pow_mem_of_mem_sup hT2 hTN
      (hHT ▸ (y : ↥H).2 : ((y : ↥H) : G) ∈ K ⊔ T)
    have h1 : quotPerm hKn e ((y : ↥H) ^ 2 ^ a) = 1 := by
      rw [map_pow, MonoidHom.mem_ker.mp y.2, one_pow]
    have h2 := (A6L24.quotPerm_eq_one_iff_of_mem hKn e _ (by simpa using ha)).mp h1
    obtain ⟨b, hb⟩ := pCoreOf_isPGroup 2 K ⟨_, h2⟩
    have hb' : (((y : ↥H) : G) ^ 2 ^ a) ^ 2 ^ b = 1 := by simpa using congrArg Subtype.val hb
    refine ⟨a + b, Subtype.ext (Subtype.ext ?_)⟩
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
    rw [pow_add, pow_mul, hb']
  have h1 : g ∈ CFSG.pCore 2 ↥H := by
    exact le_pCore 2 (MonoidHom.normal_ker _) hp (MonoidHom.mem_ker.mpr hg)
  exact (A6L24.mem_pCore_iff' g).mp h1

theorem false_of_transv_l24
    (h1334 : Stmt13_3_4) (hS : S.Hyp138) {H : Subgroup G} (hH : H ∈ S.Hz) {K : Subgroup G}
    (hK : K ∈ cComp H) (hKn : H ≤ Subgroup.normalizer (K : Set G))
    (hHK : H = K ⊔ (S.L1 ⊔ T)) {n : ℕ} (hn : 2 ≤ n) (hLie : LieF2n (↥K ⧸ CFSG.pCore 2 ↥K) n)
    (e : ↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 5)) (hhat : ¬ IsHatA6 L)
    (hL1K : S.L1 ≤ K) {x : G} (hxR : x ∈ pCoreOf 2 (S.L1 ⊔ T))
    (htr : InducesTransvMod x (conjClosure S.V3 H) (fsuV1 T V)) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKH : K ≤ H := le_of_mem_cComp hK
  have hLTH : S.L1 ⊔ T ≤ H := hH.1.1
  have hHT : H = K ⊔ T := by rw [hHK, ← sup_assoc, sup_eq_left.mpr hL1K]
  obtain ⟨p₀, -, -, -, hfix⟩ := S.exists_p0_l24 h1334 hS hH hK hKn hn hLie e
  have hxH : x ∈ H := hLTH (pCoreOf_le 2 _ hxR)
  have hV4 := S.isV4_of_mem_R1_l24 hhat hLTH hL1K hKn e hfix hxR
  have hτ1 : quotPerm hKn e ⟨x, hxH⟩ ≠ 1 := by
    intro h1
    have hQ := S.mem_QH_of_quotPerm_eq_one hH hKn hHT e ⟨x, hxH⟩ h1
    exact htr.1 ((S.mem_QH_iff hS hH hxH).mp hQ)
  obtain ⟨σ, hσs, hσ⟩ := A6L24.exists_conj_pow _ ⟨hV4.2.1, hV4.2.2, hτ1⟩
  obtain ⟨k, -, hkσ⟩ := A6L24.exists_lift hKH hKn e (Perm.mem_alternatingGroup.mpr hσs)
  have hF := (hS.hF H hH).toHypF91
  have : Fact (IsElemAbelian 2 (tildeOf (fsuV1 T V) (conjClosure S.V3 H))) :=
    ⟨hF.isElemAbelian_tilde⟩
  have hV₁ : H ≤ Subgroup.normalizer (fsuV1 T V : Set G) := hF.H_normalizes_V₁
  have hIH : H ≤ Subgroup.normalizer (conjClosure S.V3 H : Set G) :=
    le_normalizer_conjClosure S.V3 H
  have hIHN : conjClosure S.V3 H ≤ Subgroup.normalizer (fsuV1 T V : Set G) :=
    (hF.conjClosure_Vp_le_pCoreOf.trans (pCoreOf_le 2 H)).trans hV₁
  have htx := A6Tv.isTransvection_actH hV₁ hIHN hIH hxH htr
  have htx2 := B1.isTransvection_conj htx (actH hV₁ hIH k)
  obtain ⟨-, w₁, hw₁⟩ := htx
  obtain ⟨-, w₂, hw₂⟩ := htx2
  have hW : ∀ w : ↥(tildeOf (fsuV1 T V) (conjClosure S.V3 H)), w ^ 2 = 1 := fun w =>
    Subtype.ext (by
      simpa using (Fact.out : IsElemAbelian 2 (tildeOf (fsuV1 T V) (conjClosure S.V3 H))).2 w w.2)
  have h12 := A6L24.pow_twelve_of_transv hW hw₁.2 hw₂.2
  set g : ↥H := ⟨x, hxH⟩ * (k * ⟨x, hxH⟩ * k⁻¹) with hg
  have hg12 : actH hV₁ hIH (g ^ 12) = 1 := by
    rw [map_pow, hg, map_mul, map_mul, map_mul, map_inv]
    exact h12
  have hQ : ((g ^ 12 : ↥H) : G) ∈ pCoreOf 2 H :=
    (S.mem_QH_iff hS hH (g ^ 12).2).mpr ((A6Tv.actH_eq_one_iff hV₁ hIHN hIH _).mp hg12)
  have hψ := A6L24.quotPerm_eq_one_of_mem_pCoreOf hKH hKn e _ hQ
  rw [map_pow, hg, map_mul, map_mul, map_mul, map_inv, hkσ] at hψ
  apply hσ
  rw [show (24 : ℕ) = 12 * 2 by rfl, pow_mul, hψ, one_pow]

end Setting4

end CFSG.Quasithin.H13.A6
