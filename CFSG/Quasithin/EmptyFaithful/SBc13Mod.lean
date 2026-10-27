module

public import CFSG.Quasithin.EmptyFaithful.S146P14

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open scoped commutatorElement IsMulCommutative

namespace SBc13

variable {G : Type} [Group G] [Finite G] {T M H : Subgroup G} {p : ℕ} {H₀ H₁ H₂ : Subgroup G} {t : G}

theorem exists_comm_notin_of_isDecP (S : Setting146 G T M) {PQ : Subgroup G}
    (hred : IsRedCE T M H PQ p) (hdecP : IsDecP T M H p H₀ H₁ H₂ t) {u : G}
    (hu : u ∈ uHi T M H H₁) (huZ : u ∉ quasithinOmegaOneCenter T) :
    ∃ x ∈ oTwoUpper H₁, x * u * x⁻¹ * u⁻¹ ∉ quasithinOmegaOneCenter T := by
  by_contra hcon
  push Not at hcon
  have hH : IsHTM T M H := hred.isHTM
  have hTH : T ≤ H := hH.1.1
  have hHG : H ≤ mcOf T := S.le_mcOf hH
  have hH₁H : H₁ ≤ H := hdecP.le₁.trans hdecP.le
  have hH₀H : H₀ ≤ H := hdecP.le
  have hUab : IsElemAbelian 2 (conjClosure (VZ T M) H) := S.lemma_14_5_15_two hH
  have hHU : H ≤ Subgroup.normalizer (conjClosure (VZ T M) H : Set G) :=
    le_normalizer_conjClosure _ _
  have hUG : conjClosure (VZ T M) H ≤ mcOf T := fun x hx => S.mem_mcOf_of_mem_conjClosure hH hx
  have hZV : quasithinOmegaOneCenter T ≤ VZ T M := le_conjClosure _ _
  have hVU : VZ T M ≤ conjClosure (VZ T M) H := le_conjClosure _ _
  have hZU : quasithinOmegaOneCenter T ≤ conjClosure (VZ T M) H := hZV.trans hVU
  have hZc : ∀ x ∈ mcOf T, ∀ b ∈ quasithinOmegaOneCenter T, x * b = b * x :=
    fun x hx b hb => S146T.comm_Z hx hb
  have hNZ : ∀ x ∈ mcOf T, x ∈ Subgroup.normalizer (quasithinOmegaOneCenter T : Set G) :=
    fun x hx => by rw [S.normalizer_Z]; exact hx
  have hQn : ∀ h ∈ H, ∀ q ∈ pCoreOf 2 H, h * q * h⁻¹ ∈ pCoreOf 2 H := fun h hh q hq =>
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 H hh) q).mp hq
  have hQU := pCoreOf_fixes_U_mod_Z_P8 S hred
  have hUc : ∀ x ∈ conjClosure (VZ T M) H, ∀ y ∈ conjClosure (VZ T M) H, x * y = y * x :=
    fun x hx y hy => isElemAbelian_comm hUab hx hy
  have hU2 : ∀ x ∈ conjClosure (VZ T M) H, x ^ 2 = 1 := fun x hx => isElemAbelian_pow_eq_one hUab hx
  have hXH₁ : oTwoUpper H₁ ≤ H₁ := oTwoUpper_le H₁
  have hXG : oTwoUpper H₁ ≤ mcOf T := hXH₁.trans (hH₁H.trans hHG)
  have hXU : ∀ g ∈ oTwoUpper H₁, ∀ w ∈ conjClosure (VZ T M) H,
      g * w * g⁻¹ ∈ conjClosure (VZ T M) H := fun g hg w hw =>
    (Subgroup.mem_normalizer_iff.mp (hHU (hH₁H (hXH₁ hg))) w).mp hw
  have hXnQ : ∀ g ∈ oTwoUpper H₁, ∀ q ∈ pCoreOf 2 H, g * q * g⁻¹ ∈ pCoreOf 2 H :=
    fun g hg q hq => hQn g (hH₁H (hXH₁ hg)) q hq
  have hXQ : ∀ x ∈ oTwoUpper H₁, ∃ k : ℕ, x ^ p ^ k ∈ pCoreOf 2 H := fun x hx =>
    ⟨1, by simpa using hdecP.pow_mem_of_mem_oTwoUpper_P14 hred.prime hx⟩
  have hS₁H₁ : ((T ⊓ H₀) ⊓ H₁) ≤ H₁ := inf_le_right
  have hS₁T : ((T ⊓ H₀) ⊓ H₁) ≤ T := inf_le_left.trans inf_le_left
  have hS₁G : ((T ⊓ H₀) ⊓ H₁) ≤ mcOf T := (hS₁T.trans hTH).trans hHG
  have hS₁U : ∀ τ ∈ (T ⊓ H₀) ⊓ H₁, ∀ w ∈ conjClosure (VZ T M) H,
      τ * w * τ⁻¹ ∈ conjClosure (VZ T M) H := fun τ hτ w hw =>
    (Subgroup.mem_normalizer_iff.mp (hHU (hTH (hS₁T hτ))) w).mp hw
  have hS₁X : ∀ τ ∈ (T ⊓ H₀) ⊓ H₁, ∀ g ∈ oTwoUpper H₁, τ * g * τ⁻¹ ∈ oTwoUpper H₁ :=
    fun τ hτ g hg => conj_mem_oTwoUpper (Subgroup.le_normalizer (hS₁H₁ hτ)) hg
  have hZc2 : Nat.card (quasithinOmegaOneCenter T) = 2 := S.card_Z
  have hVc4 : Nat.card (VZ T M) = 4 := S.hyp.rank_two
  have hrel : (quasithinOmegaOneCenter T).relIndex (VZ T M) = 2 := by
    have e := Subgroup.relIndex_mul_card (H := quasithinOmegaOneCenter T) (K := VZ T M)
    rw [inf_eq_left.mpr hZV, hZc2, hVc4] at e
    omega
  have hne : ¬ VZ T M ≤ quasithinOmegaOneCenter T := fun hle => by
    have := Subgroup.card_le_of_le hle
    omega
  obtain ⟨v, hvV, hvZ⟩ := Set.not_subset.mp fun hs => hne (SetLike.coe_subset_coe.mp hs)
  obtain ⟨kv, hkvE, cv, hcvU, hcv, hvkc⟩ := decomp_mod_central_P7 (G₁ := mcOf T)
    (Z := quasithinOmegaOneCenter T) (U := conjClosure (VZ T M) H) (X := oTwoUpper H₁)
    (Q := pCoreOf 2 H) (T := (T ⊓ H₀) ⊓ H₁) hred.prime hred.odd hZc hUG hXG hS₁G hUc hU2 hXU
    hS₁U hS₁X hQU hXnQ hXQ (hVU hvV)
    (fun τ hτ => T_fixes_V_mod_Z_P8 S τ (hS₁T hτ) v hvV)
  have hH₁le := hdecP.le_sup_oTwoUpper_P14 S hred
  have hcvC : cv ∈ centralizerMod (quasithinOmegaOneCenter T) (conjClosure (VZ T M) H) H₁ := by
    refine ⟨hcvU, hNZ cv (hUG hcvU), fun y hy => ?_⟩
    have h1 := (quasithinOmegaOneCenter T).inv_mem (hcv y (hH₁le hy))
    have e : (y * cv * y⁻¹ * cv⁻¹)⁻¹ = cv * y * cv⁻¹ * y⁻¹ := by group
    rwa [e] at h1
  have hKU : ⁅conjClosure (VZ T M) H, oTwoUpper H₁⁆ ≤ conjClosure (VZ T M) H :=
    commutator_le_of_normalizes_P14 hXU
  have hZC : quasithinOmegaOneCenter T ≤
      centralizerMod (quasithinOmegaOneCenter T) (conjClosure (VZ T M) H) H₁ := by
    intro z hz
    refine ⟨hZU hz, hNZ z (hUG (hZU hz)), fun y hy => ?_⟩
    have hyG : y ∈ mcOf T := (hH₁H.trans hHG) hy
    have e : z * y * z⁻¹ * y⁻¹ = 1 := by
      rw [(hZc y hyG z hz).symm]
      group
    rw [e]
    exact (quasithinOmegaOneCenter T).one_mem
  set L : Subgroup G := ⁅conjClosure (VZ T M) H, oTwoUpper H₁⁆ ⊔
    centralizerMod (quasithinOmegaOneCenter T) (conjClosure (VZ T M) H) H₁ with hLdef
  have hZL : quasithinOmegaOneCenter T ≤ L := hZC.trans le_sup_right
  have hvL : v ∈ L := by
    have hz : v * (kv * cv)⁻¹ ∈ L := hZL hvkc
    have hk : kv ∈ L := Subgroup.mem_sup_left hkvE
    have hc : cv ∈ L := Subgroup.mem_sup_right hcvC
    have e : v = (v * (kv * cv)⁻¹) * kv * cv := by group
    rw [e]
    exact L.mul_mem (L.mul_mem hz hk) hc
  have hH₀X : ∀ h ∈ H₀, h ∈ Subgroup.normalizer (oTwoUpper H₁ : Set G) := fun h hh =>
    normalizer_le_normalizer_oTwoUpper_P (hdecP.H₀_le_normalizer_H₁ hh)
  have hH₀U : ∀ h ∈ H₀, h ∈ Subgroup.normalizer (conjClosure (VZ T M) H : Set G) := fun h hh =>
    hHU (hH₀H hh)
  have hH₀N : ∀ h ∈ H₀, h ∈ Subgroup.normalizer (L : Set G) := by
    intro h hh
    refine mem_normalizer_sup_P (mem_normalizer_commutator_P14 (hH₀U h hh) (hH₀X h hh)) ?_
    exact le_normalizer_centralizerMod (H := H₀) (fun x hx => hNZ x (hH₀H hx |> hHG))
      (fun x hx => hH₀U x hx) (fun x hx => hdecP.H₀_le_normalizer_H₁ hx) hh
  have hconjv : ∀ h ∈ H, h * v * h⁻¹ ∈ L := by
    intro h hh
    have hTN : T ≤ Subgroup.normalizer (H₀ : Set G) := fun x hx => hdecP.normal (hTH hx)
    have hmul := Subgroup.coe_mul_of_left_le_normalizer_right T H₀ hTN
    have hhinv : h⁻¹ ∈ (↑(T ⊔ H₀) : Set G) := by
      rw [sup_comm, ← hdecP.eq]
      exact H.inv_mem hh
    rw [hmul] at hhinv
    obtain ⟨τ, hτ, h₀, hh₀, hτh₀⟩ := Set.mem_mul.mp hhinv
    have hhe : h = h₀⁻¹ * τ⁻¹ := by
      have : h = (h⁻¹)⁻¹ := by simp
      rw [this, ← hτh₀]
      group
    have hzv : τ⁻¹ * v * τ⁻¹⁻¹ * v⁻¹ ∈ quasithinOmegaOneCenter T :=
      T_fixes_V_mod_Z_P8 S τ⁻¹ (T.inv_mem hτ) v hvV
    set z := τ⁻¹ * v * τ⁻¹⁻¹ * v⁻¹ with hz
    have hτv : τ⁻¹ * v * τ⁻¹⁻¹ = z * v := by rw [hz]; group
    have hH₀' : h₀⁻¹ ∈ H₀ := H₀.inv_mem hh₀
    have hconjL : h₀⁻¹ * v * h₀⁻¹⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp (hH₀N h₀⁻¹ hH₀') v).mp hvL
    have hzcomm : h₀⁻¹ * z = z * h₀⁻¹ := hZc _ (hH₀H hH₀' |> hHG) z hzv
    have e : h * v * h⁻¹ = z * (h₀⁻¹ * v * h₀⁻¹⁻¹) := by
      calc h * v * h⁻¹ = h₀⁻¹ * (τ⁻¹ * v * τ⁻¹⁻¹) * h₀⁻¹⁻¹ := by rw [hhe]; group
        _ = h₀⁻¹ * (z * v) * h₀⁻¹⁻¹ := by rw [hτv]
        _ = (h₀⁻¹ * z) * v * h₀⁻¹⁻¹ := by group
        _ = (z * h₀⁻¹) * v * h₀⁻¹⁻¹ := by rw [hzcomm]
        _ = z * (h₀⁻¹ * v * h₀⁻¹⁻¹) := by group
    rw [e]
    exact L.mul_mem (hZL hzv) hconjL
  have hUL : conjClosure (VZ T M) H ≤ L := by
    refine conjClosure_le fun h hh y hy => ?_
    by_cases hyZ : y ∈ quasithinOmegaOneCenter T
    · have e : h * y * h⁻¹ = y := by
        calc h * y * h⁻¹ = (y * h) * h⁻¹ := by rw [hZc h (hHG hh) y hyZ]
          _ = y := by group
      rw [e]
      exact hZL hyZ
    · have hyv : y * v⁻¹ ∈ quasithinOmegaOneCenter T :=
        mul_inv_mem_of_relIndex_two hrel hy hvV hyZ hvZ
      have hzc : h * (y * v⁻¹) * h⁻¹ = y * v⁻¹ := by
        calc h * (y * v⁻¹) * h⁻¹ = ((y * v⁻¹) * h) * h⁻¹ := by rw [hZc h (hHG hh) _ hyv]
          _ = y * v⁻¹ := by group
      have e : h * y * h⁻¹ = (y * v⁻¹) * (h * v * h⁻¹) := by
        calc h * y * h⁻¹ = (h * (y * v⁻¹) * h⁻¹) * (h * v * h⁻¹) := by group
          _ = (y * v⁻¹) * (h * v * h⁻¹) := by rw [hzc]
      rw [e]
      exact L.mul_mem (hZL hyv) (hconjv h hh)
  have hcomm : ⁅conjClosure (VZ T M) H, H₁⁆ ≤
      ⁅conjClosure (VZ T M) H, oTwoUpper H₁⁆ ⊔ quasithinOmegaOneCenter T := by
    refine Subgroup.commutator_le.mpr fun w hw y hy => ?_
    have hnorm : ⁅conjClosure (VZ T M) H, oTwoUpper H₁⁆ ≤ Subgroup.normalizer
        ((centralizerMod (quasithinOmegaOneCenter T) (conjClosure (VZ T M) H) H₁ : Subgroup G) :
          Set G) := by
      refine S146A.le_normalizer_of_forall_conj_mem fun k hk c hc => ?_
      have hkU := hKU hk
      have hcU : c ∈ conjClosure (VZ T M) H := hc.1
      have e : k * c * k⁻¹ = c := by
        calc k * c * k⁻¹ = (c * k) * k⁻¹ := by rw [hUc k hkU c hcU]
          _ = c := by group
      rw [e]
      exact hc
    have hmul := Subgroup.coe_mul_of_left_le_normalizer_right
      ⁅conjClosure (VZ T M) H, oTwoUpper H₁⁆
      (centralizerMod (quasithinOmegaOneCenter T) (conjClosure (VZ T M) H) H₁) hnorm
    have hwL : w ∈ (↑L : Set G) := hUL hw
    rw [hLdef, hmul] at hwL
    obtain ⟨k, hk, c, hc, hkc⟩ := Set.mem_mul.mp hwL
    have hyH : y ∈ H := hH₁H hy
    have hczy : c * y * c⁻¹ * y⁻¹ ∈ quasithinOmegaOneCenter T := hc.2.2 y hy
    have hkyk : y * k⁻¹ * y⁻¹ ∈ ⁅conjClosure (VZ T M) H, oTwoUpper H₁⁆ :=
      (Subgroup.mem_normalizer_iff.mp
        (mem_normalizer_commutator_P14 (hHU hyH) (le_normalizer_oTwoUpper H₁ hy)) k⁻¹).mp
        (Subgroup.inv_mem _ hk)
    have e : ⁅w, y⁆ = k * (c * y * c⁻¹ * y⁻¹) * (y * k⁻¹ * y⁻¹) := by
      rw [← hkc, commutatorElement_def]
      group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_left hk)
      (Subgroup.mem_sup_right hczy)) (Subgroup.mem_sup_left hkyk)
  have hu' : u ∈ ⁅conjClosure (VZ T M) H, H₁⁆ ⊔ quasithinOmegaOneCenter T := hu
  have hule : u ∈ ⁅conjClosure (VZ T M) H, oTwoUpper H₁⁆ ⊔ quasithinOmegaOneCenter T :=
    (sup_le hcomm le_sup_right) hu'
  have hnormZ : ⁅conjClosure (VZ T M) H, oTwoUpper H₁⁆ ≤
      Subgroup.normalizer (quasithinOmegaOneCenter T : Set G) :=
    fun k hk => hNZ k (hUG (hKU hk))
  have hmulZ := Subgroup.coe_mul_of_left_le_normalizer_right
    ⁅conjClosure (VZ T M) H, oTwoUpper H₁⁆ (quasithinOmegaOneCenter T) hnormZ
  have hule' : u ∈ (↑(⁅conjClosure (VZ T M) H, oTwoUpper H₁⁆ ⊔ quasithinOmegaOneCenter T) :
      Set G) := hule
  rw [hmulZ] at hule'
  obtain ⟨k, hk, z, hz, hkz⟩ := Set.mem_mul.mp hule'
  have hfix : ∀ g ∈ oTwoUpper H₁, g * k * g⁻¹ * k⁻¹ ∈ quasithinOmegaOneCenter T := by
    intro g hg
    have h1 := hcon g hg
    have hgz : Commute g z := hZc g (hXG hg) z hz
    have hgz' : z * g⁻¹ = g⁻¹ * z := hgz.inv_left.symm.eq
    have e : g * u * g⁻¹ * u⁻¹ = g * k * g⁻¹ * k⁻¹ := by
      rw [← hkz]
      calc g * (k * z) * g⁻¹ * (k * z)⁻¹ = g * k * (z * g⁻¹) * z⁻¹ * k⁻¹ := by group
        _ = g * k * (g⁻¹ * z) * z⁻¹ * k⁻¹ := by rw [hgz']
        _ = g * k * g⁻¹ * k⁻¹ := by group
    rw [e] at h1
    exact h1
  have hkZ : k ∈ quasithinOmegaOneCenter T :=
    comm_inf_fixed_mod_central_P14 hred.prime hred.odd (G₁ := mcOf T)
      (Z := quasithinOmegaOneCenter T) (U := conjClosure (VZ T M) H) (X := oTwoUpper H₁)
      (Q := pCoreOf 2 H) hZc hUG hXG hUc hU2 hXU hQU hXnQ hXQ k hk hfix
  apply huZ
  rw [← hkz]
  exact (quasithinOmegaOneCenter T).mul_mem hkZ hz

end SBc13

end CFSG.Quasithin
