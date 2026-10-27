module

public import CFSG.RankThree.GF2n.Tim79Defs
import CFSG.RankThree.GF2n.Tim79Swap
import CFSG.RankThree.GF2n.Tim79CentC
import CFSG.RankThree.GF2n.Tim79Mod

public section

namespace CFSG.RankThree.GF2n.Tim79

open scoped commutatorElement Matrix

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Timmesfeld

variable {G : Type} [Group G] [Finite G] {M V Q : Subgroup G}

theorem Hyp79.centralizer_L_abelian (H : Hyp79 M V Q) {g : G} (hgV : conjSubgroup g V ≠ V)
    (hgQ : conjSubgroup g V ≤ Q) :
    ∀ x ∈ Q, (∀ l ∈ Q ⊓ conjSubgroup g Q, x * l = l * x) →
      ∀ y ∈ Q, (∀ l ∈ Q ⊓ conjSubgroup g Q, y * l = l * y) → x * y = y * x := by
  classical
  obtain ⟨n, hn2, hVn, ⟨N⟩⟩ := exists_natData H hgV hgQ
  have hK4 : 4 ≤ Nat.card (GaloisField 2 n) := by
    rw [GaloisField.card 2 n (by omega)]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
  obtain ⟨hWL, hLab, -, -⟩ := H.L_facts hgV hgQ
  set Hh : Subgroup G := Q ⊔ conjSubgroup g Q with hHh
  set L : Subgroup G := Q ⊓ conjSubgroup g Q with hLdef
  set W : Subgroup G := V ⊔ conjSubgroup g V with hWdef
  set CL : Subgroup G := Subgroup.centralizer (L : Set G) with hCLdef
  have hQHh : Q ≤ Hh := le_sup_left
  have hLQ : L ≤ Q := inf_le_left
  have hVL : V ≤ L := le_sup_left.trans hWL
  have hLnorm : ∀ z ∈ Hh, ∀ l ∈ L, z * l * z⁻¹ ∈ L := H.L_normal hgV hgQ
  have hCLW : CL ≤ Subgroup.centralizer (W : Set G) := Subgroup.centralizer_le hWL
  have hLC₁ : L ≤ Q ⊓ CL := fun l hl =>
    ⟨hLQ hl, Subgroup.mem_centralizer_iff.mpr fun l' hl' => hLab l' hl' l hl⟩
  let ψ' : G → (Fin 2 → GaloisField 2 n) := fun w =>
    if h : w ∈ W then Multiplicative.toAdd (N.ψ ⟨w, h⟩) else 0
  have hψ'_eq : ∀ (w : G) (hw : w ∈ W), ψ' w = Multiplicative.toAdd (N.ψ ⟨w, hw⟩) :=
    fun w hw => dif_pos hw
  have hψ'_mul : ∀ w ∈ W, ∀ w' ∈ W, ψ' (w * w') = ψ' w + ψ' w' := by
    intro w hw w' hw'
    rw [hψ'_eq _ (mul_mem hw hw'), hψ'_eq w hw, hψ'_eq w' hw']
    have : N.ψ ⟨w * w', mul_mem hw hw'⟩ = N.ψ ⟨w, hw⟩ * N.ψ ⟨w', hw'⟩ := by
      rw [← map_mul]
      rfl
    rw [this, toAdd_mul]
  have hψ'_one : ψ' 1 = 0 := by
    rw [hψ'_eq 1 (one_mem W)]
    have : N.ψ ⟨1, one_mem W⟩ = 1 := by
      rw [← map_one N.ψ]
      rfl
    rw [this]
    rfl
  have hψ'_inj : ∀ w ∈ W, ψ' w = 0 → w = 1 := by
    intro w hw h0
    rw [hψ'_eq w hw] at h0
    have h1 : N.ψ ⟨w, hw⟩ = 1 := Multiplicative.toAdd.injective (by rw [h0]; rfl)
    have h2 : (⟨w, hw⟩ : ↥W) = 1 := N.ψ.injective (by rw [h1, map_one])
    exact congrArg Subtype.val h2
  have hψ'_conj : ∀ (z : ↥Hh) (w : G), w ∈ W →
      ψ' ((z : G) * w * (z : G)⁻¹) =
        (N.φ z : Matrix (Fin 2) (Fin 2) (GaloisField 2 n)) *ᵥ ψ' w := by
    intro z w hw
    have hw' : (z : G) * w * (z : G)⁻¹ ∈ W :=
      (Subgroup.mem_normalizer_iff.mp (N.norm z.2) w).mp hw
    rw [hψ'_eq _ hw', hψ'_eq w hw]
    exact N.compat z ⟨w, hw⟩ ⟨_, hw'⟩ rfl
  have hcoeComm : ∀ a b : ↥Hh, ((⁅a, b⁆ : ↥Hh) : G) = ⁅(a : G), (b : G)⁆ := fun a b => by
    simp [commutatorElement_def]
  have hupper : ∀ x : ↥Hh, N.φ x ∈ upperUnipotent (GaloisField 2 n) →
      ∃ q : G, q ∈ Q ∧ q⁻¹ * (x : G) ∈ Subgroup.centralizer (W : Set G) := by
    intro x hx
    have hmem : N.φ x ∈ (Q.subgroupOf Hh).map N.φ := by
      rw [N.upper]
      exact hx
    obtain ⟨q, hq, hqx⟩ := Subgroup.mem_map.mp hmem
    refine ⟨q, hq, ?_⟩
    have h1 : q⁻¹ * x ∈ N.φ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hqx, inv_mul_cancel]
    rw [N.ker, Subgroup.mem_subgroupOf] at h1
    simpa using h1
  have hLemA : ∀ x : ↥Hh, N.φ x ∈ upperUnipotent (GaloisField 2 n) →
      ∀ c ∈ Hh ⊓ CL, ⁅(x : G), c⁆ ∈ Q ⊓ CL := by
    intro x hx c hc
    obtain ⟨q, hq, hr⟩ := hupper x hx
    have hrR : q⁻¹ * (x : G) ∈ Hh ⊓ Subgroup.centralizer (W : Set G) :=
      ⟨Subgroup.mul_mem _ (Subgroup.inv_mem _ (hQHh hq)) x.2, hr⟩
    have e : ⁅(x : G), c⁆ = q * ⁅q⁻¹ * (x : G), c⁆ * q⁻¹ * ⁅q, c⁆ := by
      simp only [commutatorElement_def]; group
    rw [e]
    have h1 : q * ⁅q⁻¹ * (x : G), c⁆ * q⁻¹ ∈ L :=
      hLnorm q (hQHh hq) _ (H.comm_mem_L_of_mem_CW hgV hgQ hrR hc)
    exact Subgroup.mul_mem _ (hLC₁ h1) (H.comm_mem_inf_centralizer hgV hgQ hq hc)
  have hLemB : ∀ x : ↥Hh, N.φ x ∈ upperUnipotent (GaloisField 2 n) →
      ∀ c ∈ Q ⊓ CL, ⁅(x : G), c⁆ ∈ L := by
    intro x hx c hc
    obtain ⟨q, hq, hr⟩ := hupper x hx
    have hrR : q⁻¹ * (x : G) ∈ Hh ⊓ Subgroup.centralizer (W : Set G) :=
      ⟨Subgroup.mul_mem _ (Subgroup.inv_mem _ (hQHh hq)) x.2, hr⟩
    have hcC : c ∈ Hh ⊓ CL := ⟨hQHh hc.1, hc.2⟩
    have e : ⁅(x : G), c⁆ = q * ⁅q⁻¹ * (x : G), c⁆ * q⁻¹ * ⁅q, c⁆ := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact Subgroup.mul_mem _ (hLnorm q (hQHh hq) _ (H.comm_mem_L_of_mem_CW hgV hgQ hrR hcC))
      (hVL (H.comm_mem_V hq hc.1))
  have hfixG : ∀ c ∈ Hh ⊓ CL, (∀ z ∈ Hh, ⁅z, c⁆ ∈ L) → c ∈ L := by
    intro c hc hz
    obtain ⟨a, ha, b, hb, rfl⟩ := H.exists_mul_of_mem_C hgV hgQ hc
    have hxb : ∀ x ∈ Q, ⁅x, b⁆ ∈ L := by
      intro x hx
      have h1 := hz x (hQHh hx)
      have e : ⁅x, a * b⁆ = ⁅x, a⁆ * (a * ⁅x, b⁆ * a⁻¹) := by
        simp only [commutatorElement_def]; group
      rw [e] at h1
      have h2 : ⁅x, a⁆ ∈ L := hVL (H.comm_mem_V hx ha.1)
      have h3 : a * ⁅x, b⁆ * a⁻¹ ∈ L := by
        have := Subgroup.mul_mem _ (Subgroup.inv_mem _ h2) h1
        rwa [inv_mul_cancel_left] at this
      have hc' : (a * ⁅x, b⁆ * a⁻¹) * a = a * (a * ⁅x, b⁆ * a⁻¹) :=
        Subgroup.mem_centralizer_iff.mp ha.2 _ h3
      have e2 : ⁅x, b⁆ = a * ⁅x, b⁆ * a⁻¹ := by
        calc ⁅x, b⁆ = a⁻¹ * ((a * ⁅x, b⁆ * a⁻¹) * a) := by group
          _ = a⁻¹ * (a * (a * ⁅x, b⁆ * a⁻¹)) := by rw [hc']
          _ = a * ⁅x, b⁆ * a⁻¹ := by group
      rw [e2]
      exact h3
    have hbL : b ∈ L := H.mem_L_of_comm_mem hgV hgQ hb.1 hxb
    obtain ⟨m, hmH, hm1, -⟩ := H.exists_swap hgV hgQ
    have hmb : ⁅m, b⁆ ∈ L := by
      rw [commutatorElement_def]
      exact Subgroup.mul_mem _ (hLnorm m hmH b hbL) (Subgroup.inv_mem _ hbL)
    have h1 := hz m hmH
    have e : ⁅m, a * b⁆ = ⁅m, a⁆ * (a * ⁅m, b⁆ * a⁻¹) := by
      simp only [commutatorElement_def]; group
    rw [e] at h1
    have h3 : a * ⁅m, b⁆ * a⁻¹ = ⁅m, b⁆ := by
      have := Subgroup.mem_centralizer_iff.mp ha.2 _ hmb
      calc a * ⁅m, b⁆ * a⁻¹ = (a * ⁅m, b⁆) * a⁻¹ := rfl
        _ = (⁅m, b⁆ * a) * a⁻¹ := by rw [this]
        _ = ⁅m, b⁆ := by group
    rw [h3] at h1
    have hma : ⁅m, a⁆ ∈ L := by
      have := Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ hmb)
      rwa [mul_inv_cancel_right] at this
    have hmaL : m * a * m⁻¹ ∈ L := by
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · rw [show m * a * m⁻¹ = ⁅m, a⁆ * a by rw [commutatorElement_def]; group]
        exact Subgroup.mul_mem _ (hLQ hma) ha.1
      · rw [← hm1, mem_conjSubgroup]
        simpa [mul_assoc] using ha.1
    have := hLnorm m⁻¹ (Subgroup.inv_mem _ hmH) _ hmaL
    have haL : a ∈ L := by simpa [mul_assoc] using this
    exact Subgroup.mul_mem _ haL hbL
  have hVW : V ≤ W := le_sup_left
  let β : ↥Hh → ↥Hh → (Fin 2 → GaloisField 2 n) := fun a b => ψ' ⁅(a : G), (b : G)⁆
  have key : ∀ a ∈ (Hh ⊓ CL).subgroupOf Hh, ∀ b ∈ (Hh ⊓ CL).subgroupOf Hh, β a b = 0 := by
    refine eq_zero_of_equivariant_pairing hK4 N.φ N.surj ((Hh ⊓ CL).subgroupOf Hh)
      (L.subgroupOf Hh) ((Q ⊓ CL).subgroupOf Hh) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ β ?_ ?_ ?_ ?_ ?_
    ·
      exact fun l hl => hLC₁ hl
    ·
      exact fun z hz => ⟨hQHh hz.1, hz.2⟩
    ·
      intro z c hc
      exact H.conj_mem_C hgV hgQ z.2 hc
    ·
      exact fun z l hl => hLnorm z z.2 l hl
    ·
      intro a ha b hb
      show ((⁅a, b⁆ : ↥Hh) : G) ∈ L
      rw [hcoeComm]
      exact hWL (H.comm_mem_W_of_mem_C hgV hgQ ha hb)
    ·
      intro z hz c hc
      have hz' : z ∈ N.φ.ker := hz
      rw [N.ker, Subgroup.mem_subgroupOf] at hz'
      show ((⁅z, c⁆ : ↥Hh) : G) ∈ L
      rw [hcoeComm]
      exact H.comm_mem_L_of_mem_CW hgV hgQ ⟨z.2, hz'⟩ hc
    ·
      intro c hc hz
      show (c : G) ∈ L
      refine hfixG c hc fun z' hz' => ?_
      have h2 : ((⁅(⟨z', hz'⟩ : ↥Hh), c⁆ : ↥Hh) : G) ∈ L := hz ⟨z', hz'⟩
      rwa [hcoeComm] at h2
    ·
      intro x x' hx hx' c hc
      show ((⁅x', ⁅x, c⁆⁆ : ↥Hh) : G) ∈ L
      rw [hcoeComm, hcoeComm]
      exact hLemB x' hx' _ (hLemA x hx c hc)
    ·
      intro c hc x hx
      show ((⁅x, c⁆ : ↥Hh) : G) ∈ L
      rw [hcoeComm]
      exact hLemB x hx c hc
    ·
      intro S hLS hSC hSn hC₁S
      refine le_antisymm hSC fun c hc => ?_
      have hcG : (c : G) ∈ Hh ⊓ CL := hc
      obtain ⟨a, ha, b, hb, hcab⟩ := H.exists_mul_of_mem_C hgV hgQ hcG
      obtain ⟨m, hmH, hm1, -⟩ := H.exists_swap hgV hgQ
      have haH : a ∈ Hh := hQHh ha.1
      have hbH : b ∈ Hh := Subgroup.mem_sup_right hb.1
      have haS : (⟨a, haH⟩ : ↥Hh) ∈ S := hC₁S ha
      have hb₁Q : m⁻¹ * b * m ∈ Q := by
        have : b ∈ conjSubgroup m Q := by
          rw [hm1]
          exact hb.1
        exact mem_conjSubgroup.mp this
      have hb₁C : m⁻¹ * b * m ∈ CL := by
        refine Subgroup.mem_centralizer_iff.mpr fun l hl => ?_
        have h1 : m * l * m⁻¹ ∈ L := hLnorm m hmH l hl
        have h2 := Subgroup.mem_centralizer_iff.mp hb.2 _ h1
        calc l * (m⁻¹ * b * m) = m⁻¹ * ((m * l * m⁻¹) * b) * m := by group
          _ = m⁻¹ * (b * (m * l * m⁻¹)) * m := by rw [h2]
          _ = (m⁻¹ * b * m) * l := by group
      have hb₁H : m⁻¹ * b * m ∈ Hh :=
        Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hmH) hbH) hmH
      have hb₁S : (⟨m⁻¹ * b * m, hb₁H⟩ : ↥Hh) ∈ S := hC₁S ⟨hb₁Q, hb₁C⟩
      have hbS : (⟨b, hbH⟩ : ↥Hh) ∈ S := by
        have := hSn ⟨m, hmH⟩ _ hb₁S
        convert this using 1
        ext
        simp [mul_assoc]
      have hcS : c = ⟨a, haH⟩ * ⟨b, hbH⟩ := by
        ext
        exact hcab
      rw [hcS]
      exact S.mul_mem haS hbS
    ·
      intro a ha a' ha' b hb
      show ψ' ⁅((a * a' : ↥Hh) : G), (b : G)⁆ = ψ' ⁅(a : G), (b : G)⁆ + ψ' ⁅(a' : G), (b : G)⁆
      have hW1 : ⁅(a' : G), (b : G)⁆ ∈ W := H.comm_mem_W_of_mem_C hgV hgQ ha' hb
      have hW0 : ⁅(a : G), (b : G)⁆ ∈ W := H.comm_mem_W_of_mem_C hgV hgQ ha hb
      have hcent : (a : G) * ⁅(a' : G), (b : G)⁆ = ⁅(a' : G), (b : G)⁆ * (a : G) :=
        (Subgroup.mem_centralizer_iff.mp (hCLW ha.2) _ hW1).symm
      have e : ⁅((a * a' : ↥Hh) : G), (b : G)⁆ = ⁅(a' : G), (b : G)⁆ * ⁅(a : G), (b : G)⁆ := by
        have e0 : ⁅((a * a' : ↥Hh) : G), (b : G)⁆ =
            (a : G) * ⁅(a' : G), (b : G)⁆ * (a : G)⁻¹ * ⁅(a : G), (b : G)⁆ := by
          simp only [Subgroup.coe_mul, commutatorElement_def]; group
        rw [e0, hcent]
        group
      rw [e, hψ'_mul _ hW1 _ hW0, add_comm]
    ·
      intro a ha b hb b' hb'
      show ψ' ⁅(a : G), ((b * b' : ↥Hh) : G)⁆ = ψ' ⁅(a : G), (b : G)⁆ + ψ' ⁅(a : G), (b' : G)⁆
      have hW1 : ⁅(a : G), (b : G)⁆ ∈ W := H.comm_mem_W_of_mem_C hgV hgQ ha hb
      have hW0 : ⁅(a : G), (b' : G)⁆ ∈ W := H.comm_mem_W_of_mem_C hgV hgQ ha hb'
      have hcent : (b : G) * ⁅(a : G), (b' : G)⁆ = ⁅(a : G), (b' : G)⁆ * (b : G) :=
        (Subgroup.mem_centralizer_iff.mp (hCLW hb.2) _ hW0).symm
      have e : ⁅(a : G), ((b * b' : ↥Hh) : G)⁆ = ⁅(a : G), (b : G)⁆ * ⁅(a : G), (b' : G)⁆ := by
        have e0 : ⁅(a : G), ((b * b' : ↥Hh) : G)⁆ =
            ⁅(a : G), (b : G)⁆ * ((b : G) * ⁅(a : G), (b' : G)⁆ * (b : G)⁻¹) := by
          simp only [Subgroup.coe_mul, commutatorElement_def]; group
        rw [e0, hcent]
        group
      rw [e, hψ'_mul _ hW1 _ hW0]
    ·
      intro l hl b hb
      show ψ' ⁅(l : G), (b : G)⁆ = 0
      have hcom : ⁅(l : G), (b : G)⁆ = 1 :=
        commutatorElement_eq_one_iff_mul_comm.mpr (Subgroup.mem_centralizer_iff.mp hb.2 (l : G) hl)
      rw [hcom, hψ'_one]
    ·
      intro a ha l hl
      show ψ' ⁅(a : G), (l : G)⁆ = 0
      have hcom : ⁅(a : G), (l : G)⁆ = 1 :=
        commutatorElement_eq_one_iff_mul_comm.mpr
          (Subgroup.mem_centralizer_iff.mp ha.2 (l : G) hl).symm
      rw [hcom, hψ'_one]
    ·
      intro z a ha b hb
      show ψ' ⁅((z * a * z⁻¹ : ↥Hh) : G), ((z * b * z⁻¹ : ↥Hh) : G)⁆ = _
      have e : ⁅((z * a * z⁻¹ : ↥Hh) : G), ((z * b * z⁻¹ : ↥Hh) : G)⁆ =
          (z : G) * ⁅(a : G), (b : G)⁆ * (z : G)⁻¹ := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def]; group
      rw [e, hψ'_conj z ⁅(a : G), (b : G)⁆ (H.comm_mem_W_of_mem_C hgV hgQ ha hb)]
  intro x hx hxL y hy hyL
  have hxC : (⟨x, hQHh hx⟩ : ↥Hh) ∈ (Hh ⊓ CL).subgroupOf Hh :=
    ⟨hQHh hx, Subgroup.mem_centralizer_iff.mpr fun l hl => (hxL l hl).symm⟩
  have hyC : (⟨y, hQHh hy⟩ : ↥Hh) ∈ (Hh ⊓ CL).subgroupOf Hh :=
    ⟨hQHh hy, Subgroup.mem_centralizer_iff.mpr fun l hl => (hyL l hl).symm⟩
  have hk : ψ' ⁅x, y⁆ = 0 := key _ hxC _ hyC
  exact commutatorElement_eq_one_iff_mul_comm.mp
    (hψ'_inj _ (hVW (H.comm_mem_V hx hy)) hk)

end CFSG.RankThree.GF2n.Tim79
