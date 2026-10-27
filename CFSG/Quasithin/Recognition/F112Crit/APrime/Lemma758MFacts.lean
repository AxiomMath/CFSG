module

public import CFSG.Quasithin.Recognition.F112Crit.APrime.Lemma758Defs
public import CFSG.Quasithin.Recognition.F112Crit.APrime.S3Gamma1
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.F112Crit.APrime

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F7

variable {G : Type} [Group G] [Finite G] {G₀ G₁ G₂ T L : Subgroup G}

private theorem pCoreOf_le_G₂ (hA : AmalgamS3 G₀ G₁ G₂ T L) : pCoreOf 2 G₁ ≤ G₂ := by
  intro x hx
  exact (hA.hyp.T_le (isSylowTwoOf_pCoreOf_le hA.hyp.sylow₁ hx)).2

private theorem pCoreOf_le_G₁ (hA : AmalgamS3 G₀ G₁ G₂ T L) : pCoreOf 2 G₂ ≤ G₁ := by
  intro x hx
  exact (hA.hyp.T_le (isSylowTwoOf_pCoreOf_le hA.hyp.sylow₂ hx)).1

private theorem conjClosure_le_G₂ (hA : AmalgamS3 G₀ G₁ G₂ T L) :
    conjClosure (pCoreOf 2 G₁) G₂ ≤ G₂ := by
  refine conjClosure_le fun g hg z hz => ?_
  exact G₂.mul_mem (G₂.mul_mem hg (pCoreOf_le_G₂ hA hz)) (G₂.inv_mem hg)

theorem AmalgamS3.conjClosure_le_L (hA : AmalgamS3 G₀ G₁ G₂ T L) :
    conjClosure (pCoreOf 2 G₁) G₂ ≤ L := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine conjClosure_le fun g hg z hz => ?_
  have hPleG₂ : conjSub g (pCoreOf 2 G₁) ≤ G₂ := by
    intro y hy
    rw [mem_conjSub] at hy
    have hyG₂ : g⁻¹ * y * g ∈ G₂ := pCoreOf_le_G₂ hA hy
    have : g * (g⁻¹ * y * g) * g⁻¹ ∈ G₂ :=
      G₂.mul_mem (G₂.mul_mem hg hyG₂) (G₂.inv_mem hg)
    simpa [mul_assoc] using this
  exact hA.le_L_of_isPGroup hPleG₂ (isPGroup_conjSub (pCoreOf_isPGroup 2 G₁))
    (mul_mem_conjSub hz)

private theorem isSylowTwoOf_conjClosure
    (h3 : (pCoreOf 2 G₁).relIndex (conjClosure (pCoreOf 2 G₁) G₂) = 3) :
    IsSylowTwoOf (pCoreOf 2 G₁) (conjClosure (pCoreOf 2 G₁) G₂) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨le_conjClosure _ _, pCoreOf_isPGroup 2 G₁, ?_⟩
  change ¬ 2 ∣ (pCoreOf 2 G₁).relIndex (conjClosure (pCoreOf 2 G₁) G₂)
  rw [h3]
  norm_num

private theorem conjClosure_card
    (h3 : (pCoreOf 2 G₁).relIndex (conjClosure (pCoreOf 2 G₁) G₂) = 3) :
    ∃ a : ℕ, Nat.card (conjClosure (pCoreOf 2 G₁) G₂) = 2 ^ a * 3 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp (pCoreOf_isPGroup 2 G₁)
  refine ⟨a, ?_⟩
  have hmul := Subgroup.relIndex_mul_card (pCoreOf 2 G₁)
    (conjClosure (pCoreOf 2 G₁) G₂)
  rw [inf_eq_left.mpr (le_conjClosure (pCoreOf 2 G₁) G₂)] at hmul
  rw [h3] at hmul
  rw [← hmul, ha]
  ring

private theorem conjClosure_inf_eq (hA : AmalgamS3 G₀ G₁ G₂ T L)
    (h3 : (pCoreOf 2 G₁).relIndex (conjClosure (pCoreOf 2 G₁) G₂) = 3) :
    conjClosure (pCoreOf 2 G₁) G₂ ⊓ G₁ = pCoreOf 2 G₁ := by
  let M := conjClosure (pCoreOf 2 G₁) G₂
  have hQleM : pCoreOf 2 G₁ ≤ M := le_conjClosure _ _
  have hQleG₁ : pCoreOf 2 G₁ ≤ G₁ := pCoreOf_le 2 G₁
  refine le_antisymm ?_ (le_inf hQleM hQleG₁)
  have hQleI : pCoreOf 2 G₁ ≤ M ⊓ G₁ := le_inf hQleM hQleG₁
  have hprod : (pCoreOf 2 G₁).relIndex (M ⊓ G₁) * (M ⊓ G₁).relIndex M =
      (pCoreOf 2 G₁).relIndex M :=
    Subgroup.relIndex_mul_relIndex (pCoreOf 2 G₁) (M ⊓ G₁) M hQleI inf_le_left
  rw [show (pCoreOf 2 G₁).relIndex M = 3 from h3] at hprod
  have hdvd : (pCoreOf 2 G₁).relIndex (M ⊓ G₁) ∣ 3 :=
    ⟨(M ⊓ G₁).relIndex M, hprod.symm⟩
  rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3'
  · exact Subgroup.relIndex_eq_one.mp h1
  · exfalso
    have hIrel : (M ⊓ G₁).relIndex M = 1 := by
      rw [h3'] at hprod
      omega
    have hMG₁ : M ≤ G₁ := (Subgroup.relIndex_eq_one.mp hIrel).trans inf_le_right
    have hMT : M ≤ T := by
      rw [← hA.inf_eq]
      exact le_inf (AmalgamS3.conjClosure_le_L hA) hMG₁
    have hM2 : IsPGroup 2 M := hA.hyp.sylow₂.2.1.to_le hMT
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨b, hb⟩ := IsPGroup.iff_card.mp hM2
    obtain ⟨a, ha⟩ := conjClosure_card h3
    have h3dvd : 3 ∣ Nat.card M := by
      rw [ha]
      exact ⟨2 ^ a, by ring⟩
    rw [hb] at h3dvd
    exact (by norm_num : ¬ (3 : ℕ) ∣ 2) (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3dvd)

private theorem conjClosure_sup_eq (hA : AmalgamS3 G₀ G₁ G₂ T L)
    (h3 : (pCoreOf 2 G₁).relIndex (conjClosure (pCoreOf 2 G₁) G₂) = 3) :
    conjClosure (pCoreOf 2 G₁) G₂ ⊔ (G₁ ⊓ G₂) = G₂ := by
  let M := conjClosure (pCoreOf 2 G₁) G₂
  let H := G₁ ⊓ G₂
  have hMleG₂ : M ≤ G₂ := conjClosure_le_G₂ hA
  have hMH : M ⊔ H ≤ G₂ := sup_le hMleG₂ inf_le_right
  have hMnotG₁ : ¬ M ≤ G₁ := by
    intro hMG₁
    have hMleQ : M ≤ pCoreOf 2 G₁ := by
      rw [← conjClosure_inf_eq hA h3]
      exact le_inf le_rfl hMG₁
    have hQleM : pCoreOf 2 G₁ ≤ M := le_conjClosure _ _
    have hMeq : M = pCoreOf 2 G₁ := le_antisymm hMleQ hQleM
    have hrel : (pCoreOf 2 G₁).relIndex M = 1 := by
      rw [← hMeq]
      exact Subgroup.relIndex_self M
    rw [hrel] at h3
    norm_num at h3
  have hprod : H.relIndex (M ⊔ H) * (M ⊔ H).relIndex G₂ = H.relIndex G₂ :=
    Subgroup.relIndex_mul_relIndex H (M ⊔ H) G₂ le_sup_right hMH
  rw [show H.relIndex G₂ = 3 from hA.relIndex_inf_G₂] at hprod
  have hdvd : H.relIndex (M ⊔ H) ∣ 3 := ⟨(M ⊔ H).relIndex G₂, hprod.symm⟩
  have hne1 : H.relIndex (M ⊔ H) ≠ 1 := by
    intro h1
    have hMleH : M ⊔ H ≤ H := Subgroup.relIndex_eq_one.mp h1
    exact hMnotG₁ ((le_sup_left : M ≤ M ⊔ H).trans (hMleH.trans inf_le_left))
  rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3'
  · exact absurd h1 hne1
  · have hlast : (M ⊔ H).relIndex G₂ = 1 := by
      rw [h3'] at hprod
      omega
    exact le_antisymm hMH (Subgroup.relIndex_eq_one.mp hlast)

private theorem conjClosure_pCoreOf_ne_bot
    (h3 : (pCoreOf 2 G₁).relIndex (conjClosure (pCoreOf 2 G₁) G₂) = 3) :
    pCoreOf 2 G₁ ≠ ⊥ := by
  intro hbot
  have hMbot : conjClosure (pCoreOf 2 G₁) G₂ = ⊥ := by
    rw [hbot]
    refine le_antisymm ?_ bot_le
    exact conjClosure_le fun g _ z hz => by
      rw [Subgroup.mem_bot] at hz ⊢
      simp [hz]
  rw [hMbot, hbot] at h3
  rw [Subgroup.relIndex_self (⊥ : Subgroup G)] at h3
  norm_num at h3

private theorem conjClosure_not_le_normalizer (hA : AmalgamS3 G₀ G₁ G₂ T L)
    (h3 : (pCoreOf 2 G₁).relIndex (conjClosure (pCoreOf 2 G₁) G₂) = 3) :
    ¬ conjClosure (pCoreOf 2 G₁) G₂ ≤
      Subgroup.normalizer (pCoreOf 2 G₁ : Set G) := by
  intro hMN
  let M := conjClosure (pCoreOf 2 G₁) G₂
  let H := G₁ ⊓ G₂
  have hQne : pCoreOf 2 G₁ ≠ ⊥ := conjClosure_pCoreOf_ne_bot h3
  have hsup : M ⊔ H = G₂ := conjClosure_sup_eq hA h3
  have hHN : H ≤ Subgroup.normalizer (pCoreOf 2 G₁ : Set G) :=
    inf_le_left.trans (le_normalizer_pCoreOf 2 G₁)
  have hG₂N : G₂ ≤ Subgroup.normalizer (pCoreOf 2 G₁ : Set G) := by
    rw [← hsup]
    exact sup_le hMN hHN
  have hG₀N : G₀ ≤ Subgroup.normalizer (pCoreOf 2 G₁ : Set G) := by
    rw [hA.hyp.gen]
    exact sup_le (le_normalizer_pCoreOf 2 G₁) hG₂N
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQleG₀ : pCoreOf 2 G₁ ≤ G₀ := (pCoreOf_le 2 G₁).trans hA.hyp.le₁
  have hQleO₂ : pCoreOf 2 G₁ ≤ pCoreOf 2 G₀ :=
    le_pCoreOf_of_le_normalizer 2 hQleG₀ hG₀N (pCoreOf_isPGroup 2 G₁)
  rw [hA.hyp.o2_trivial] at hQleO₂
  exact hQne (le_bot_iff.mp hQleO₂)

private theorem conjClosure_pCoreOf_eq (hA : AmalgamS3 G₀ G₁ G₂ T L)
    (hD : G₂ ≤ Subgroup.normalizer
      ((pCoreOf 2 G₁ ⊓ pCoreOf 2 G₂ : Subgroup G) : Set G))
    (h3 : (pCoreOf 2 G₁).relIndex (conjClosure (pCoreOf 2 G₁) G₂) = 3) :
    pCoreOf 2 (conjClosure (pCoreOf 2 G₁) G₂) =
      pCoreOf 2 G₁ ⊓ pCoreOf 2 G₂ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let M := conjClosure (pCoreOf 2 G₁) G₂
  let D := pCoreOf 2 G₁ ⊓ pCoreOf 2 G₂
  have hMleG₂ : M ≤ G₂ := conjClosure_le_G₂ hA
  have hDleQ₁ : D ≤ pCoreOf 2 G₁ := inf_le_left
  have hDleM : D ≤ M := hDleQ₁.trans (le_conjClosure _ _)
  have hD2 : IsPGroup 2 D := (pCoreOf_isPGroup 2 G₁).to_le hDleQ₁
  have hDnorm : M ≤ Subgroup.normalizer (D : Set G) := hMleG₂.trans hD
  have hDleO₂ : D ≤ pCoreOf 2 M :=
    le_pCoreOf_of_le_normalizer 2 hDleM hDnorm hD2
  have hSyl : IsSylowTwoOf (pCoreOf 2 G₁) M := isSylowTwoOf_conjClosure h3
  have hO₂leQ₁ : pCoreOf 2 M ≤ pCoreOf 2 G₁ := isSylowTwoOf_pCoreOf_le hSyl
  have hO₂leQ₂ : pCoreOf 2 M ≤ pCoreOf 2 G₂ := by
    have hO₂leG₂ : pCoreOf 2 M ≤ G₂ := (pCoreOf_le 2 M).trans hMleG₂
    have hG₂normM : G₂ ≤ Subgroup.normalizer (M : Set G) := le_normalizer_conjClosure _ _
    have hG₂normO : G₂ ≤ Subgroup.normalizer (pCoreOf 2 M : Set G) :=
      hG₂normM.trans (normalizer_le_normalizer_pCoreOf 2 M)
    exact le_pCoreOf_of_le_normalizer 2 hO₂leG₂ hG₂normO (pCoreOf_isPGroup 2 M)
  refine le_antisymm ?_ hDleO₂
  exact le_inf hO₂leQ₁ hO₂leQ₂

private theorem conjClosure_commutator_mem (hA : AmalgamS3 G₀ G₁ G₂ T L)
    (hD : G₂ ≤ Subgroup.normalizer
      ((pCoreOf 2 G₁ ⊓ pCoreOf 2 G₂ : Subgroup G) : Set G)) :
    ∀ x ∈ conjClosure (pCoreOf 2 G₁) G₂, ∀ q ∈ pCoreOf 2 G₂,
      x * q * x⁻¹ * q⁻¹ ∈ pCoreOf 2 G₁ ⊓ pCoreOf 2 G₂ := by
  let Q₁ := pCoreOf 2 G₁
  let Q₂ := pCoreOf 2 G₂
  let D := Q₁ ⊓ Q₂
  have hQ₁G₂ : Q₁ ≤ G₂ := pCoreOf_le_G₂ hA
  have hQ₂G₁ : Q₂ ≤ G₁ := pCoreOf_le_G₁ hA
  have hQ₂G₂ : Q₂ ≤ G₂ := pCoreOf_le 2 G₂
  let K : Subgroup G :=
    { carrier := {x | x ∈ G₂ ∧ ∀ q ∈ Q₂, x * q * x⁻¹ * q⁻¹ ∈ D}
      one_mem' := by
        refine ⟨G₂.one_mem, fun q _ => ?_⟩
        simpa using D.one_mem
      mul_mem' := by
        intro x y hx hy
        obtain ⟨hxG₂, hx'⟩ := hx
        obtain ⟨hyG₂, hy'⟩ := hy
        refine ⟨G₂.mul_mem hxG₂ hyG₂, fun q hq => ?_⟩
        let d₁ := y * q * y⁻¹ * q⁻¹
        have hd₁D : d₁ ∈ D := hy' q hq
        have hxnorm : x ∈ Subgroup.normalizer (D : Set G) := hD hxG₂
        have hconj : x * d₁ * x⁻¹ ∈ D :=
          (Subgroup.mem_normalizer_iff.mp hxnorm d₁).mp hd₁D
        have hcalc : (x * y) * q * (x * y)⁻¹ * q⁻¹ =
            (x * d₁ * x⁻¹) * (x * q * x⁻¹ * q⁻¹) := by
          dsimp [d₁]
          group
        rw [hcalc]
        exact D.mul_mem hconj (hx' q hq)
      inv_mem' := by
        intro x hx
        obtain ⟨hxG₂, hx'⟩ := hx
        refine ⟨G₂.inv_mem hxG₂, fun q hq => ?_⟩
        let d := x * q * x⁻¹ * q⁻¹
        have hdD : d ∈ D := hx' q hq
        have hxinvnorm : x⁻¹ ∈ Subgroup.normalizer (D : Set G) :=
          Subgroup.inv_mem _ (hD hxG₂)
        have hd' : x⁻¹ * d * x ∈ D := by
          have := (Subgroup.mem_normalizer_iff.mp hxinvnorm d).mp hdD
          simpa using this
        have hcalc : x⁻¹ * q * x⁻¹⁻¹ * q⁻¹ = (x⁻¹ * d * x)⁻¹ := by
          dsimp [d]
          group
        rw [hcalc]
        exact D.inv_mem hd' }
  have hgen : ∀ g ∈ G₂, ∀ z ∈ Q₁, g * z * g⁻¹ ∈ K := by
    intro g hg z hz
    have hxG₂ : g * z * g⁻¹ ∈ G₂ :=
      G₂.mul_mem (G₂.mul_mem hg (hQ₁G₂ hz)) (G₂.inv_mem hg)
    refine ⟨hxG₂, fun q hq => ?_⟩
    have hx_conjQ₁ : g * z * g⁻¹ ∈ conjSub g Q₁ := mul_mem_conjSub hz
    have hQ₂conj : conjSub g Q₂ = Q₂ :=
      conjSub_eq_of_mem_normalizer (le_normalizer_pCoreOf 2 G₂ hg)
    have hq_conjG₁ : q ∈ conjSub g G₁ := by
      have hq' : q ∈ conjSub g Q₂ := by rw [hQ₂conj]; exact hq
      exact conjSub_mono g hQ₂G₁ hq'
    have hnorm : conjSub g G₁ ≤ Subgroup.normalizer (conjSub g Q₁ : Set G) :=
      conjSub_le_normalizer (g := g) (le_normalizer_pCoreOf 2 G₁)
    have hqx : q * (g * z * g⁻¹) * q⁻¹ ∈ conjSub g Q₁ :=
      (Subgroup.mem_normalizer_iff.mp (hnorm hq_conjG₁) (g * z * g⁻¹)).mp hx_conjQ₁
    have hcomm_conj : (g * z * g⁻¹) * q * (g * z * g⁻¹)⁻¹ * q⁻¹ ∈ conjSub g Q₁ := by
      have hcalc : (g * z * g⁻¹) * q * (g * z * g⁻¹)⁻¹ * q⁻¹ =
          (g * z * g⁻¹) * (q * (g * z * g⁻¹) * q⁻¹)⁻¹ := by group
      rw [hcalc]
      exact (conjSub g Q₁).mul_mem hx_conjQ₁ ((conjSub g Q₁).inv_mem hqx)
    have hcomm_Q₂ : (g * z * g⁻¹) * q * (g * z * g⁻¹)⁻¹ * q⁻¹ ∈ Q₂ := by
      have hxN : g * z * g⁻¹ ∈ Subgroup.normalizer (Q₂ : Set G) :=
        le_normalizer_pCoreOf 2 G₂ hxG₂
      have hqx₂ : (g * z * g⁻¹) * q * (g * z * g⁻¹)⁻¹ ∈ Q₂ :=
        (Subgroup.mem_normalizer_iff.mp hxN q).mp hq
      exact Q₂.mul_mem hqx₂ (Q₂.inv_mem hq)
    have hDconj : conjSub g D = D := conjSub_eq_of_mem_normalizer (hD hg)
    have hinter : conjSub g Q₁ ⊓ Q₂ = D := by
      rw [← hQ₂conj, ← conjSub_inf]
      simpa [D] using hDconj
    have hmem : (g * z * g⁻¹) * q * (g * z * g⁻¹)⁻¹ * q⁻¹ ∈ conjSub g Q₁ ⊓ Q₂ :=
      ⟨hcomm_conj, hcomm_Q₂⟩
    rwa [hinter] at hmem
  have hMK : conjClosure Q₁ G₂ ≤ K := conjClosure_le hgen
  intro x hx q hq
  exact (hMK hx).2 q hq

private theorem conjClosure_charTwo (hA : AmalgamS3 G₀ G₁ G₂ T L)
    (hD : G₂ ≤ Subgroup.normalizer
      ((pCoreOf 2 G₁ ⊓ pCoreOf 2 G₂ : Subgroup G) : Set G))
    (h3 : (pCoreOf 2 G₁).relIndex (conjClosure (pCoreOf 2 G₁) G₂) = 3) :
    CharTwo (conjClosure (pCoreOf 2 G₁) G₂) := by
  let M := conjClosure (pCoreOf 2 G₁) G₂
  let Q₁ := pCoreOf 2 G₁
  let Q₂ := pCoreOf 2 G₂
  let D := Q₁ ⊓ Q₂
  let C := M ⊓ Subgroup.centralizer (D : Set G)
  have hMleG₂ : M ≤ G₂ := conjClosure_le_G₂ hA
  have hpceq : pCoreOf 2 M = D := conjClosure_pCoreOf_eq hA hD h3
  have hcomm := conjClosure_commutator_mem hA hD
  have hno3 : ¬ 3 ∣ Nat.card ↥C := by
    intro h3dvd
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨x, hxorder⟩ := exists_prime_orderOf_dvd_card' (G := ↥C) 3 h3dvd
    have hxmem : (x : G) ∈ M ⊓ Subgroup.centralizer (D : Set G) :=
      show (x : G) ∈ C from x.2
    have hxM : (x : G) ∈ M := hxmem.1
    have hxC : (x : G) ∈ Subgroup.centralizer (D : Set G) := hxmem.2
    have hxordG : orderOf (x : G) = 3 := (Subgroup.orderOf_coe x).trans hxorder
    have hnot : False := by
      have hd_eq : ∀ q ∈ Q₂, (x : G) * q * (x : G)⁻¹ * q⁻¹ = 1 := by
        intro q hq
        let d := (x : G) * q * (x : G)⁻¹ * q⁻¹
        have hdD : d ∈ D := hcomm (x : G) hxM q hq
        have hxd : (x : G) * d = d * (x : G) :=
          (Subgroup.mem_centralizer_iff.mp hxC d hdD).symm
        have hxq : (x : G) * q * (x : G)⁻¹ = d * q := by
          dsimp [d]
          group
        have hxdn : ∀ n : ℕ, (x : G) * d ^ n * (x : G)⁻¹ = d ^ n := by
          intro n
          have hpow : (x : G) * d ^ n = d ^ n * (x : G) := by
            induction n with
            | zero => simp
            | succ n ih =>
              calc (x : G) * d ^ (n + 1) = (x : G) * d ^ n * d := by group
                _ = d ^ n * (x : G) * d := by rw [ih]
                _ = d ^ n * ((x : G) * d) := by group
                _ = d ^ n * (d * (x : G)) := by rw [hxd]
                _ = d ^ (n + 1) * (x : G) := by group
          calc (x : G) * d ^ n * (x : G)⁻¹ = d ^ n * (x : G) * (x : G)⁻¹ := by rw [hpow]
            _ = d ^ n := by group
        have hpowq : ∀ n : ℕ, (x : G) ^ n * q * ((x : G) ^ n)⁻¹ = d ^ n * q := by
          intro n
          induction n with
          | zero => simp
          | succ n ih =>
            calc (x : G) ^ (n + 1) * q * ((x : G) ^ (n + 1))⁻¹
                = (x : G) * ((x : G) ^ n * q * ((x : G) ^ n)⁻¹) * (x : G)⁻¹ := by group
              _ = (x : G) * (d ^ n * q) * (x : G)⁻¹ := by rw [ih]
              _ = ((x : G) * d ^ n * (x : G)⁻¹) * ((x : G) * q * (x : G)⁻¹) := by group
              _ = d ^ n * (d * q) := by rw [hxdn n, hxq]
              _ = d ^ (n + 1) * q := by group
        have hx3 : (x : G) ^ 3 = 1 := by rw [← hxordG, pow_orderOf_eq_one]
        have hd3 : d ^ 3 = 1 := by
          have h := hpowq 3
          simp only [hx3, one_mul, inv_one] at h
          have h' := congrArg (fun t => t * q⁻¹) h
          simpa [mul_assoc] using h'.symm
        haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
        have hD2 : IsPGroup 2 D := (pCoreOf_isPGroup 2 G₁).to_le inf_le_left
        obtain ⟨m, hm⟩ := hD2 ⟨d, hdD⟩
        have hmval : d ^ (2 ^ m) = 1 := by
          simpa using congrArg Subtype.val hm
        have hcop : Nat.Coprime (2 ^ m) 3 :=
          (by norm_num : Nat.Coprime 2 3).pow_left m
        have hd1 : d = 1 := (pow_eq_one_iff_of_coprime hcop).1 ⟨hmval, hd3⟩
        simpa [d] using hd1
      have hxcent : (x : G) ∈ Subgroup.centralizer (Q₂ : Set G) := by
        refine Subgroup.mem_centralizer_iff.mpr fun q hq => ?_
        have h1 : (x : G) * q * (x : G)⁻¹ * q⁻¹ = 1 := hd_eq q hq
        have hxq : (x : G) * q * (x : G)⁻¹ = q := by
          have := congrArg (fun t => t * q) h1
          simpa [mul_assoc] using this
        calc q * (x : G) = ((x : G) * q * (x : G)⁻¹) * (x : G) := by rw [hxq]
          _ = (x : G) * q := by group
      have hxQ₂ : (x : G) ∈ Q₂ := hA.charTwo₂ ⟨hMleG₂ hxM, hxcent⟩
      obtain ⟨m, hm⟩ := (pCoreOf_isPGroup 2 G₂) ⟨(x : G), hxQ₂⟩
      have hmval : (x : G) ^ (2 ^ m) = 1 := by
        simpa using congrArg Subtype.val hm
      have hx3 : (x : G) ^ 3 = 1 := by rw [← hxordG, pow_orderOf_eq_one]
      have hcop : Nat.Coprime (2 ^ m) 3 :=
        (by norm_num : Nat.Coprime 2 3).pow_left m
      have hx1 : (x : G) = 1 := (pow_eq_one_iff_of_coprime hcop).1 ⟨hmval, hx3⟩
      rw [hx1] at hxordG
      norm_num at hxordG
    exact hnot
  obtain ⟨a, ha⟩ := conjClosure_card h3
  have hCdvdM : Nat.card ↥C ∣ Nat.card ↥M := Subgroup.card_dvd_of_le inf_le_left
  rw [ha] at hCdvdM
  have hcop : Nat.Coprime (Nat.card ↥C) 3 :=
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hno3).symm
  have hCdvd2 : Nat.card ↥C ∣ 2 ^ a := (hcop.dvd_mul_right).mp hCdvdM
  have hCp : IsPGroup 2 C := IsPGroup.of_card_dvd_pow (n := a) hCdvd2
  have hMD : M ≤ Subgroup.normalizer (D : Set G) := hMleG₂.trans hD
  have hMcent : M ≤
      Subgroup.normalizer (Subgroup.centralizer (D : Set G) : Set G) := by
    intro m hm
    apply CosetGeom.mem_normalizer_of_conjSub_eq
    have hmD : conjSub m D = D := conjSub_eq_of_mem_normalizer (hMD hm)
    rw [← conjSub_centralizer m D, hmD]
  have hCnorm : M ≤ Subgroup.normalizer (C : Set G) :=
    le_normalizer_inf Subgroup.le_normalizer hMcent
  have hCle : C ≤ pCoreOf 2 M :=
    le_pCoreOf_of_le_normalizer 2 inf_le_left hCnorm hCp
  rw [hpceq] at hCle
  change M ⊓ Subgroup.centralizer (pCoreOf 2 M : Set G) ≤ pCoreOf 2 M
  rw [hpceq]
  exact hCle

theorem AmalgamS3.parabolicA_conjClosure (hA : AmalgamS3 G₀ G₁ G₂ T L)
    (hD : G₂ ≤ Subgroup.normalizer
      ((pCoreOf 2 G₁ ⊓ pCoreOf 2 G₂ : Subgroup G) : Set G))
    (h3 : (pCoreOf 2 G₁).relIndex (conjClosure (pCoreOf 2 G₁) G₂) = 3) :
    ParabolicA G₁ G₂ (conjClosure (pCoreOf 2 G₁) G₂) where
  le := conjClosure_le_G₂ hA
  le_normalizer := le_normalizer_conjClosure _ _
  le_conjClosure := le_rfl
  isSylowTwoOf := isSylowTwoOf_conjClosure h3
  relIndex := h3
  not_le_normalizer := conjClosure_not_le_normalizer hA h3
  pCoreOf_eq := conjClosure_pCoreOf_eq hA hD h3
  charTwo := conjClosure_charTwo hA hD h3
  card := conjClosure_card h3
  sup_eq := conjClosure_sup_eq hA h3
  inf_eq := conjClosure_inf_eq hA h3
  commutator_mem := conjClosure_commutator_mem hA hD

end CFSG.Quasithin.F112Crit.APrime

end
