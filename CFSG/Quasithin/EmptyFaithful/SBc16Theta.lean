module

public import CFSG.Quasithin.EmptyFaithful.SBc13A3Main
public import CFSG.Quasithin.EmptyFaithful.SBc14Pair
public import CFSG.Quasithin.EmptyFaithful.F918C1
public import CFSG.Quasithin.EmptyFaithful.S146P14

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open scoped commutatorElement

namespace SBc16

variable {G : Type} [Group G] [Finite G] {T M H : Subgroup G} {p : ℕ} {H₀ H₁ H₂ K₁ K₂ : Subgroup G}
  {t s : G}

theorem gap3Theta_of_kerAct (S : Setting146 G T M) {PQ : Subgroup G} (hp5 : p = 5)
    (hred : IsRedCE T M H PQ p) (hdec : IsDecP T M H p H₀ H₁ H₂ t)
    (hK₁ : K₁ = oTwoUpper H₁) (hK₂ : K₂ = oTwoUpper H₂)
    (hset : Setup14615 T M H H₁ H₂ K₁ K₂ s)
    (hker : ∀ x ∈ mcOf T, orderOf x = 5 →
      x ∈ SBc14.kerAct (oTwoUpper H) (pCoreOf 2 (oTwoUpper H))) :
    Gap3Theta T K₁ K₂ := by
  subst hp5 hK₁ hK₂
  have hp : Nat.Prime 5 := by norm_num
  have hdec' : IsDecP T M H 5 H₀ H₂ H₁ t⁻¹ := hdec.swap
  have hH : IsHTM T M H := hred.isHTM
  have hHG : H ≤ mcOf T := S.le_mcOf hH
  have hQ2 : IsPGroup 2 (pCoreOf 2 H) := pCoreOf_isPGroup 2 H
  have hQn : ∀ h ∈ H, ∀ q ∈ pCoreOf 2 H, h * q * h⁻¹ ∈ pCoreOf 2 H := fun h hh q hq =>
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 H hh) q).mp hq
  have hKX : oTwoUpper H = oTwoUpper H₁ ⊔ oTwoUpper H₂ := hdec.oTwoUpper_eq S hred
  have hKH : oTwoUpper H ≤ H := oTwoUpper_le H
  have hKG : oTwoUpper H ≤ mcOf T := hKH.trans hHG
  have hKn : ∀ g ∈ mcOf T, ∀ k ∈ oTwoUpper H, g * k * g⁻¹ ∈ oTwoUpper H := by
    intro g hg k hk
    have := mem_conjClosure hg hk
    rwa [hset.kz, ← hKX] at this
  have hRK : pCoreOf 2 (oTwoUpper H) ≤ oTwoUpper H := pCoreOf_le 2 _
  have hR2 : IsPGroup 2 (pCoreOf 2 (oTwoUpper H)) := pCoreOf_isPGroup 2 _
  have hRn : ∀ g ∈ mcOf T, ∀ r ∈ pCoreOf 2 (oTwoUpper H), g * r * g⁻¹ ∈ pCoreOf 2 (oTwoUpper H) := by
    intro g hg r hr
    have hgK : g ∈ Subgroup.normalizer (oTwoUpper H : Set G) :=
      S146A.le_normalizer_of_forall_conj_mem (L := mcOf T) (K := oTwoUpper H) hKn hg
    exact (Subgroup.mem_normalizer_iff.mp
      (normalizer_le_normalizer_pCoreOf 2 (oTwoUpper H) hgK) r).mp hr
  have hRQ : pCoreOf 2 (oTwoUpper H) ≤ pCoreOf 2 H :=
    le_pCoreOf_of_le_normalizer 2 (hRK.trans hKH)
      ((le_normalizer_oTwoUpper H).trans (normalizer_le_normalizer_pCoreOf 2 (oTwoUpper H))) hR2
  have hKQR : ∀ c ∈ oTwoUpper H, c ∈ pCoreOf 2 H → c ∈ pCoreOf 2 (oTwoUpper H) := by
    intro c hcK hcQ
    have hn : oTwoUpper H ≤ Subgroup.normalizer ((oTwoUpper H ⊓ pCoreOf 2 H : Subgroup G) : Set G) :=
      S146A.le_normalizer_of_forall_conj_mem fun g hg x hx =>
        ⟨(oTwoUpper H).mul_mem ((oTwoUpper H).mul_mem hg hx.1) ((oTwoUpper H).inv_mem hg),
          hQn g (hKH hg) x hx.2⟩
    have hle : oTwoUpper H ⊓ pCoreOf 2 H ≤ pCoreOf 2 (oTwoUpper H) :=
      le_pCoreOf_of_le_normalizer 2 inf_le_left hn (hQ2.to_le inf_le_right)
    exact hle ⟨hcK, hcQ⟩
  obtain ⟨a₁, ha₁X, ha₁o⟩ := hdec.exists_order_p_P14 hp (by norm_num)
  obtain ⟨a₂, ha₂X, ha₂o⟩ := hdec'.exists_order_p_P14 hp (by norm_num)
  have hneQ : ∀ a : G, orderOf a = 5 → a ∉ pCoreOf 2 H := by
    intro a hao haQ
    obtain ⟨k, hk⟩ := hQ2 ⟨a, haQ⟩
    have hk' : a ^ 2 ^ k = 1 := congrArg Subtype.val hk
    have hd : orderOf a ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
    rw [hao] at hd
    have := Nat.Prime.dvd_of_dvd_pow hp hd
    omega
  have ha₁Q := hneQ a₁ ha₁o
  have ha₂Q := hneQ a₂ ha₂o
  have ha₁p : a₁ ^ 5 = 1 := by rw [← ha₁o]; exact pow_orderOf_eq_one a₁
  have ha₂p : a₂ ^ 5 = 1 := by rw [← ha₂o]; exact pow_orderOf_eq_one a₂
  have ha₁K : a₁ ∈ oTwoUpper H := by
    rw [hKX]
    exact Subgroup.mem_sup_left ha₁X
  have ha₂K : a₂ ∈ oTwoUpper H := by
    rw [hKX]
    exact Subgroup.mem_sup_right ha₂X
  have ha₁H₁ : a₁ ∈ H₁ := oTwoUpper_le H₁ ha₁X
  have ha₂H₂ : a₂ ∈ H₂ := oTwoUpper_le H₂ ha₂X
  have hcommQ : a₁ * a₂ * a₁⁻¹ * a₂⁻¹ ∈ pCoreOf 2 H :=
    hdec.comm (Subgroup.commutator_mem_commutator ha₁H₁ ha₂H₂)
  have hcomm : a₁ * a₂ * a₁⁻¹ * a₂⁻¹ ∈ pCoreOf 2 (oTwoUpper H) :=
    hKQR _ ((oTwoUpper H).mul_mem ((oTwoUpper H).mul_mem ((oTwoUpper H).mul_mem ha₁K ha₂K)
      ((oTwoUpper H).inv_mem ha₁K)) ((oTwoUpper H).inv_mem ha₂K)) hcommQ
  have ha₁R : a₁ ∉ pCoreOf 2 (oTwoUpper H) := fun h => ha₁Q (hRQ h)
  have ha₂R : a₂ ∉ pCoreOf 2 (oTwoUpper H) := fun h => ha₂Q (hRQ h)
  have hind : ∀ m : ℤ, a₁ ^ m * a₂⁻¹ ∈ pCoreOf 2 (oTwoUpper H) → False := by
    intro m hm
    have h1 : a₁ ^ m * a₂⁻¹ ∈ pCoreOf 2 H := hRQ hm
    have hm₁ : a₁ ^ m ∈ H₁ := H₁.zpow_mem ha₁H₁ m
    have h2 : a₁ ^ m ∈ H₂ := by
      have e : a₁ ^ m = (a₁ ^ m * a₂⁻¹) * a₂ := by group
      rw [e]
      exact H₂.mul_mem (hdec.Q₂ h1) ha₂H₂
    have h3 : a₁ ^ m ∈ pCoreOf 2 H := by
      rw [← hdec.inf]
      exact ⟨hm₁, h2⟩
    have h4 : a₁ ^ m ∈ pCoreOf 2 (oTwoUpper H) :=
      hKQR _ ((oTwoUpper H).zpow_mem ha₁K m) h3
    apply ha₂R
    have h5 : a₂⁻¹ ∈ pCoreOf 2 (oTwoUpper H) := by
      have e : a₂⁻¹ = (a₁ ^ m)⁻¹ * (a₁ ^ m * a₂⁻¹) := by group
      rw [e]
      exact (pCoreOf 2 (oTwoUpper H)).mul_mem ((pCoreOf 2 (oTwoUpper H)).inv_mem h4) hm
    simpa using (pCoreOf 2 (oTwoUpper H)).inv_mem h5
  intro x hxG hxo
  by_contra hxK
  have hx5 : x ^ 5 = 1 := by rw [← hxo]; exact pow_orderOf_eq_one x
  have hrank : CFSG.Open.pRank 5 (⊤ : Subgroup ↥(mcOf T)) ≤ 2 :=
    (S.sqtkGroup_of_isHTM S.isHTM_mcOf).1 5 hp (by norm_num)
  have hxker := SBc14.mem_kerAct.mp (hker x hxG hxo)
  refine SBc13.core_sub_prime_A3 (G₁ := mcOf T) (K := oTwoUpper H)
    (R := pCoreOf 2 (oTwoUpper H)) (a₁ := a₁) (a₂ := a₂) (x := x) hp (by norm_num) hrank hKG hR2
    hRn hRK ha₁K ha₂K ha₁p ha₂p ha₁R ha₂R hcomm hind hxG hx5 (by rw [hKX]; exact hxK) ?_ ?_
  · exact ⟨1, by simpa using hxker.2 a₁ ha₁K⟩
  · exact ⟨1, by simpa using hxker.2 a₂ ha₂K⟩

end SBc16

end CFSG.Quasithin
