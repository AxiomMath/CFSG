module

public import CFSG.Quasithin.Vol2.Ch11SecO10L
public import CFSG.Quasithin.Vol2.Ch11SecE42S3a
public import CFSG.Quasithin.Vol2.Ch11SecE44Nat
public import CFSG.Quasithin.Vol2.Ch11SecO10J
public import CFSG.Quasithin.Vol2.Ch11SecO10K

public section

namespace CFSG.Quasithin.Vol2.Ch11.O10

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.H13 SecE

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ} {V₁ : Subgroup G} {z : G}

theorem false_of_rOf_eq_rOf_two (hF43 : Facts43) (hF44 : Facts44) (hF15 : SecA.Facts15)
    (hN : SecA.NatFacts) (h331 : Stmt3_3_1) (h1102 : Stmt11_0_2) (h1103 : Stmt11_0_3)
    (h1104 : Stmt11_0_4) (h1110 : Stmt11_1_0) (h1111 : Stmt11_1_1) (h1115 : Stmt11_1_5)
    (h1141 : Stmt11_4_1) (hc : Conf11_4_2 T L I n V₁ z) {I' V'₁ V'₂ : Subgroup G}
    (hK : Hyp11 G T (kz L V₁ z) I' n)
    (hk : KindSL3 (kz L V₁ z) (fsuV T I') n ∨ KindSp4 (kz L V₁ z) (fsuV T I') n)
    (hV'₁ : IsVi T (kz L V₁ z) I' n 1 V'₁) (hV'₂ : IsVi T (kz L V₁ z) I' n 2 V'₂)
    (hLK : LOf L V₁ ≤ LOf (kz L V₁ z) V'₂) (hR : ROf T L V₁ = ROf T (kz L V₁ z) V'₂) :
    False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := hc.hyp
  have hn : 2 ≤ n := h.one_lt
  obtain ⟨-, -, hKz, -, -, hzV₁⟩ := conf_spec hF43 h1102 h1110 h1111 h1141 hc
  obtain ⟨X, hX⟩ := SecD.exists_isCartanX h
  have hcV := (h1141 G T L I n V₁ X h hc.vi hX).1.1
  obtain ⟨X', hX'⟩ := SecD.exists_isCartanX hK
  have hcV' := (h1141 G T _ I' n V'₁ X' hK hV'₁ hX').1.1
  have hR2 := rOf_two_le hN h331 h1102 hK hcV' hk hV'₁ hV'₂
  have hVZ : V'₂ ≤ omegaOneCenterOf (ROf T L V₁) := by
    intro v hv
    have hvV : v ∈ fsuV T I' := SecA.IsVi.le_fsuV hV'₂ hv
    unfold omegaOneCenterOf omegaOneOf
    refine Subgroup.subset_closure ⟨⟨?_, ?_⟩, (SecA.isElemAbelian_fsuV hK).2 v hvV⟩
    · rw [hR]
      exact SecA.fsuV_le_ROf hK hvV
    · rw [hR]
      exact Subgroup.mem_centralizer_iff.mpr fun r hr =>
        (Subgroup.mem_centralizer_iff.mp (hR2 hr).2 v hv).symm
  have hNR : Subgroup.normalizer (ROf T L V₁ : Set G) ≤ Subgroup.normalizer (L : Set G) := by
    rcases h1115 G T L I n V₁ h hc.vi with hle | ⟨-, -, -, hV₁eq⟩
    · exact hle
    · exfalso
      have hle : V'₂ ≤ V₁ := by
        rw [hV₁eq]
        exact hVZ
      have h1 := SecA.IsVi.relIndex_eq hc.vi
      have h2 := SecA.IsVi.relIndex_eq hV'₂
      rw [hcV, Subgroup.relIndex_bot_left] at h1
      rw [hcV', Subgroup.relIndex_bot_left] at h2
      have h3 := Subgroup.card_le_of_le hle
      rw [h1, h2] at h3
      have h4 : 2 ^ (n * 1) < 2 ^ (n * 2) := Nat.pow_lt_pow_right (by norm_num) (by omega)
      omega
  obtain ⟨c, hcx, hp, hpd⟩ := exists_mem_xOne_two hN h1102 hK hV'₁ hV'₂ hX'
  have hcX' : c ∈ X' := hcx.1
  have hcK : c ∈ kz L V₁ z := (hX'.1 hcX').1
  have hcR : c ∈ Subgroup.normalizer (ROf T L V₁ : Set G) := by
    rw [hR]
    exact cartan_le_normalizer_rOf_of_le hN h1102 hK (Or.inr rfl) hV'₂ hX'
      (hR2.trans inf_le_left) hcX'
  have hcM := hNR hcR
  have hcz : c ∈ Subgroup.centralizer ({z} : Set G) := hKz hcK
  have hcN : c ∈ Subgroup.normalizer (fsuV T I : Set G) :=
    mem_normalizer_fsuV_of_TI h1103 h (SecA.IsVi.le_fsuV hc.vi hzV₁) hc.ne_one hcM hcz
  have hcV₁ := mem_normalizer_V₁ hF15 h1102 h hcV hc.vi hcN hcR
  have hcL := mem_L_of_prime h1102 h1104 h hcM hcN hp hpd
  have hcL₁ : c ∈ Subgroup.normalizer (LOf L V₁ : Set G) := SecD.mem_normalizer_lOf hcM hcV₁
  have hcS : c ∈ sectionCentralizer (LOf L V₁) (pCoreOf 2 (LOf L V₁)) := by
    refine ⟨hcL₁, CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _ hcL₁,
      fun l hl => ?_⟩
    have h1 : c * l * c⁻¹ * l⁻¹ ∈ LOf L V₁ :=
      (LOf L V₁).mul_mem ((Subgroup.mem_normalizer_iff.mp hcL₁ l).mp hl) ((LOf L V₁).inv_mem hl)
    have h2 : c * l * c⁻¹ * l⁻¹ ∈ pCoreOf 2 (LOf (kz L V₁ z) V'₂) := hcx.2.2.2 l (hLK hl)
    have hle : LOf L V₁ ⊓ pCoreOf 2 (LOf (kz L V₁ z) V'₂) ≤ pCoreOf 2 (LOf L V₁) :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left
        (fun y hy => SecD.mem_normalizer_inf (Subgroup.le_normalizer hy)
          (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _ (hLK hy)))
        ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _).to_le inf_le_right)
    exact hle ⟨h1, h2⟩
  obtain ⟨a, ha⟩ := isTwo_of_mem_L hF44 h1102 h hcV hc.vi hzV₁ hc.ne_one hcL hcz hcS
  have h2 : orderOf c = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp
    (hp.dvd_of_dvd_pow (orderOf_dvd_of_pow_eq_one ha))
  rw [h2] at hpd
  obtain ⟨e, he⟩ := hpd
  obtain ⟨d, hd⟩ : 2 ∣ 2 ^ n := dvd_pow_self 2 (by omega)
  have : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  omega

end CFSG.Quasithin.Vol2.Ch11.O10
