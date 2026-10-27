module

public import CFSG.Quasithin.Background.CommVCommute
public import CFSG.Quasithin.H13.A6S13816g
public import CFSG.Quasithin.Background.G64Linear
public import CFSG.Quasithin.EmptyFaithful.S1565L17

public section

namespace CFSG.Quasithin.H13.A6

open CFSG.Open CFSG.Quasithin

namespace SzMod

variable {W : Type} [CommGroup W]

theorem map_mem_commV {X : Subgroup (MulAut W)} {σ : MulAut W} (hσ : ∀ x ∈ X, σ * x = x * σ)
    {u : W} (hu : u ∈ commV X) : σ u ∈ commV X :=
  CFSG.Quasithin.apply_mem_commV_of_forall_commute hσ hu

theorem map_mem_fixV {X : Subgroup (MulAut W)} {σ : MulAut W} (hσ : ∀ x ∈ X, σ * x = x * σ)
    {u : W} (hu : u ∈ fixV X) : σ u ∈ fixV X := by
  intro x hx
  have e : σ (x u) = x (σ u) := by
    simpa [MulAut.mul_apply] using congrArg (fun φ : MulAut W => φ u) (hσ x hx)
  rw [← e, hu x hx]

theorem map_mem_fixV_of_conj {X : Subgroup (MulAut W)} {t : MulAut W}
    (ht : ∀ x ∈ X, t⁻¹ * x * t ∈ X) {u : W} (hu : u ∈ fixV X) : t u ∈ fixV X := by
  intro x hx
  have h1 := hu _ (ht x hx)
  rw [MulAut.mul_apply, MulAut.mul_apply] at h1
  calc x (t u) = t (t⁻¹ (x (t u))) := by simp
    _ = t u := by rw [h1]

theorem false_of_binaryNaturalSz_le {L : Subgroup (MulAut W)} {U Z : Subgroup W} {f : ℕ}
    (h : BinaryNaturalSz L U Z f) (hUZ : U ≤ Z) : False := by
  obtain ⟨a, -, -, K, _, _, -, π, -, -, -, -, -, -, -, β, hβs, hβk, -⟩ := h
  obtain ⟨u, hu⟩ := hβs (QuotientGroup.mk
    ⟨Multiplicative.ofAdd (Pi.single (0 : Fin 4) (1 : K) : Fin 4 → K), trivial⟩)
  rw [(hβk u).mpr (hUZ u.2)] at hu
  have h2 := (QuotientGroup.eq_one_iff _).mp hu.symm
  have h3 : Multiplicative.ofAdd (Pi.single (0 : Fin 4) (1 : K) : Fin 4 → K) ∈
      (⊥ : Subgroup (Multiplicative (Fin 4 → K))) := Subgroup.mem_subgroupOf.mp h2
  have h4 := congrFun (congrArg Multiplicative.toAdd (Subgroup.mem_bot.mp h3)) 0
  simp at h4

theorem realizesVia_injective {D : FFModel} (hD : D.Faithful) {L : Subgroup (MulAut W)}
    {U Z : Subgroup W} {π : D.Gam →* ↥L} (h : D.RealizesVia L U Z π) :
    Function.Injective π :=
  CFSG.Quasithin.FFModel.RealizesVia.injective_of_faithful_on hD h

theorem three_dvd_card_of_natural_sl2 {L : Subgroup (MulAut W)} {U Z : Subgroup W} {n : ℕ}
    (h : BinaryNaturalSL L U Z 2 n) : 3 ∣ Nat.card ↥L := by
  obtain ⟨K, _, _, hK, π, hπ⟩ := h
  have hinj := realizesVia_injective (FFModel.nat_faithful _) hπ
  have hcard : Nat.card ↥L = Nat.card ↥(CFSG.Assembly.LowTwoRank.StatedSL 2 K) :=
    (Nat.card_congr (Equiv.ofBijective π ⟨hinj, hπ.1⟩)).symm
  have := Fintype.ofFinite K
  rw [hcard, CFSG.Quasithin.Vol2.Ch10.SecA.card_statedSL_two K, ← Nat.card_eq_fintype_card, hK]
  have h4 : (2 ^ n) ^ 2 % 3 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, Nat.pow_mod]
    norm_num
  have h5 : 3 ∣ (2 ^ n) ^ 2 - 1 := by
    have : 1 ≤ (2 ^ n) ^ 2 := Nat.one_le_pow _ _ (by positivity)
    omega
  exact h5.mul_left _

theorem false_of_szEnd [Finite W] (hW : ∀ w : W, w ^ 2 = 1) (hSzE : SzEnd)
    {Mp L : Subgroup (MulAut W)} {σ t : MulAut W} (hσ3 : σ ^ 3 = 1)
    (hfpf : ∀ w : W, σ w = w → w = 1) (hσMp : ∀ m ∈ Mp, σ * m = m * σ) (hLMp : L ≤ Mp)
    (htL : ∀ h ∈ L, t * h * t⁻¹ ∈ Mp) (htMp : ∀ m ∈ Mp, t * m * t⁻¹ ∈ Mp)
    (htMp' : ∀ m ∈ Mp, t⁻¹ * m * t ∈ Mp)
    (hsum : IsSumMod (fixV Mp) (commV L) ((commV L).map t.toMonoidHom) ⊤) {f : ℕ}
    (hSz : BinaryNaturalSz L (commV L) (commV L ⊓ fixV Mp) f) : False := by
  have hσL : ∀ h ∈ L, σ * h = h * σ := fun h hh => hσMp h (hLMp hh)
  obtain ⟨σ', hσ'⟩ : ∃ σ', σ' = t⁻¹ * σ * t := ⟨_, rfl⟩
  have hσ'3 : σ' ^ 3 = 1 := by
    rw [hσ', show t⁻¹ * σ * t = t⁻¹ * σ * t⁻¹⁻¹ by rw [inv_inv], conj_pow, hσ3, mul_one,
      mul_inv_cancel]
  have hσ'L : ∀ h ∈ L, σ' * h = h * σ' := by
    intro h hh
    have e := hσMp _ (htL h hh)
    calc σ' * h = t⁻¹ * (σ * (t * h * t⁻¹)) * t := by rw [hσ']; group
      _ = t⁻¹ * ((t * h * t⁻¹) * σ) * t := by rw [e]
      _ = h * σ' := by rw [hσ']; group
  have hσF : ∀ u ∈ fixV Mp, σ u ∈ fixV Mp := fun u hu => map_mem_fixV hσMp hu
  have htF : ∀ u ∈ fixV Mp, t u ∈ fixV Mp := fun u hu => map_mem_fixV_of_conj htMp' hu
  have htF' : ∀ u ∈ fixV Mp, t⁻¹ u ∈ fixV Mp := fun u hu =>
    map_mem_fixV_of_conj (fun m hm => by simpa using htMp m hm) hu
  have hσ'F : ∀ u ∈ fixV Mp, σ' u ∈ fixV Mp := fun u hu => by
    rw [hσ', MulAut.mul_apply, MulAut.mul_apply]
    exact htF' _ (hσF _ (htF u hu))
  have h1 := hSzE W L (commV L) (commV L ⊓ fixV Mp) f hSz σ ⟨1, by rw [pow_one]; exact hσ3⟩
    (fun u hu => map_mem_commV hσL hu) (fun u hu => ⟨map_mem_commV hσL hu.1, hσF u hu.2⟩) hσL
  have h2 := hSzE W L (commV L) (commV L ⊓ fixV Mp) f hSz σ' ⟨1, by rw [pow_one]; exact hσ'3⟩
    (fun u hu => map_mem_commV hσ'L hu) (fun u hu => ⟨map_mem_commV hσ'L hu.1, hσ'F u hu.2⟩)
    hσ'L
  let Q : Subgroup W :=
    { carrier := {w | σ w * w⁻¹ ∈ fixV Mp}
      one_mem' := by simp
      mul_mem' := fun {a b} ha hb => by
        have e : σ (a * b) * (a * b)⁻¹ = (σ a * a⁻¹) * (σ b * b⁻¹) := by
          rw [map_mul, mul_inv]
          ac_rfl
        show σ (a * b) * (a * b)⁻¹ ∈ fixV Mp
        rw [e]
        exact (fixV Mp).mul_mem ha hb
      inv_mem' := fun {a} ha => by
        have e : σ a⁻¹ * a⁻¹⁻¹ = (σ a * a⁻¹)⁻¹ := by
          rw [map_inv, inv_inv, mul_inv, inv_inv]
        show σ a⁻¹ * a⁻¹⁻¹ ∈ fixV Mp
        rw [e]
        exact (fixV Mp).inv_mem ha }
  have hQ : ∀ w : W, σ w * w⁻¹ ∈ fixV Mp := by
    have hUQ : commV L ≤ Q := fun u hu => (h1 u hu).2
    have hUtQ : (commV L).map t.toMonoidHom ≤ Q := by
      rintro _ ⟨u, hu, rfl⟩
      have e : σ (t u) = t (σ' u) := by
        rw [hσ', MulAut.mul_apply, MulAut.mul_apply]
        simp
      show σ (t u) * (t u)⁻¹ ∈ fixV Mp
      rw [e, ← map_inv, ← map_mul]
      exact htF _ (h2 u hu).2
    have hFQ : fixV Mp ≤ Q := fun u hu => (fixV Mp).mul_mem (hσF u hu) ((fixV Mp).inv_mem hu)
    have htop : (⊤ : Subgroup W) ≤ Q := by
      rw [hsum.1]
      exact sup_le (sup_le hUQ hUtQ) hFQ
    exact fun w => htop (Subgroup.mem_top w)
  have hall : ∀ w : W, w ∈ fixV Mp := by
    intro w
    obtain ⟨g, hg⟩ : ∃ g, g = σ w * w⁻¹ := ⟨_, rfl⟩
    have hn : G64.norm3 σ w = 1 :=
      hfpf _ (G64.fixV_zpowers_iff.mp (G64.norm3_mem_fixV σ hσ3 w))
    rw [G64.norm3_apply] at hn
    have e1 : σ w = g * w := by rw [hg, inv_mul_cancel_right]
    have e2 : σ (σ w) = σ g * (g * w) := by rw [e1, map_mul, e1]
    rw [e2, e1] at hn
    have hw2 : w * w = 1 := by rw [← sq, hW]
    have hg2 : g * g = 1 := by rw [← sq, hW]
    have e3 : w * (g * w) * (σ g * (g * w)) = (w * w) * (g * g) * (w * σ g) := by ac_rfl
    rw [e3, hw2, hg2, one_mul, one_mul] at hn
    rw [eq_inv_of_mul_eq_one_left hn]
    exact (fixV Mp).inv_mem (hσF g (hg ▸ hQ w))
  exact false_of_binaryNaturalSz_le hSz fun u hu => ⟨hu, hall u⟩

theorem false_of_modFiveIii [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    (hSzE : SzEnd) {Mp T L : Subgroup (MulAut W)} {V : Subgroup W} {σ t : MulAut W} {n : ℕ}
    (hL : IsSz n ↥L) (hσ3 : σ ^ 3 = 1) (hfpf : ∀ w : W, σ w = w → w = 1)
    (hσMp : ∀ m ∈ Mp, σ * m = m * σ) (hLMp : L ≤ Mp) (htL : ∀ h ∈ L, t * h * t⁻¹ ∈ Mp)
    (htMp : ∀ m ∈ Mp, t * m * t⁻¹ ∈ Mp) (htMp' : ∀ m ∈ Mp, t⁻¹ * m * t ∈ Mp)
    (h : ModFiveIii Mp T L V t) : False := by
  obtain ⟨hsum, -, hcase⟩ := h
  have h3 := SzCase.not_three_dvd_of_isSz hL
  obtain ⟨a₀, ha₀, hn⟩ : ∃ a₀, 1 ≤ a₀ ∧ n = 2 * a₀ + 1 := by
    obtain ⟨-, a, ha, -, -, -, hf, -⟩ := hL
    exact ⟨a, ha, hf⟩
  have hn3 : 3 ≤ n := by omega
  have hodd : Odd n := ⟨a₀, hn⟩
  have h504 := le_card_of_psl2_or_sz hn3 (Or.inr hL)
  have h168 : ¬ IsPSL 3 2 1 ↥L := fun hp => h3 (by
    rw [SBc11.card_of_isPSL_three_two hp]
    norm_num)
  rcases hcase with ⟨⟨hcomm, hmod⟩, -⟩ | hB | hD2 | hD3
  · rcases hmod with ⟨n', hn'⟩ | h31 | ⟨f, hf⟩ | ⟨a, ha1, ha⟩ | h5
    · exact h3 (three_dvd_card_of_natural_sl2 hn')
    · have := card_le_168_of_natural_sl3 h31
      omega
    · rw [← hcomm] at hf
      exact false_of_szEnd hW hSzE hσ3 hfpf hσMp hLMp htL htMp htMp' hsum hf
    · exact orthExcl_of W n hn3 hodd L V _ (Or.inr hL) ⟨a, ha1, ha⟩
    · have := card_le_sixty_of_alternating_five h5
      omega
  · exact h168 hB.1
  · exact h168 hD2.1
  · obtain ⟨n', hpsl, -⟩ := hD3
    exact h3 (L2Case.three_dvd_card (Or.inl ⟨n', hpsl⟩))

theorem false_of_modFive [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    (hSzE : SzEnd) {M Mp T L : Subgroup (MulAut W)} {V : Subgroup W} {σ t : MulAut W} {n : ℕ}
    (hL : IsSz n ↥L) (hσ3 : σ ^ 3 = 1) (hfpf : ∀ w : W, σ w = w → w = 1)
    (hσMp : ∀ m ∈ Mp, σ * m = m * σ) (hMp : Mp = L ⊔ conjAutSub t L)
    (htMp : t ∈ Subgroup.normalizer (Mp : Set (MulAut W))) (h : ModFive M Mp T L V t) :
    False := by
  have h3 := SzCase.not_three_dvd_of_isSz hL
  have hdvd : Nat.card ↥(autSub L V) ∣ Nat.card ↥L := by
    refine (Subgroup.card_map_dvd _ _).trans ?_
    have e : Nat.card ↥(L.subgroupOf (stabSub V)) = Nat.card ↥(L ⊓ stabSub V) := by
      rw [← Subgroup.card_subtype (stabSub V) (L.subgroupOf (stabSub V)),
        Subgroup.subgroupOf_map_subtype]
    rw [e]
    exact Subgroup.card_dvd_of_le inf_le_left
  have htMp1 : ∀ m ∈ Mp, t * m * t⁻¹ ∈ Mp := fun m hm =>
    (Subgroup.mem_normalizer_iff.mp htMp m).mp hm
  have htMp2 : ∀ m ∈ Mp, t⁻¹ * m * t ∈ Mp := fun m hm => by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ htMp) m).mp hm
    simpa using this
  have hLMp : L ≤ Mp := by
    rw [hMp]
    exact le_sup_left
  have hLtMp : conjAutSub t L ≤ Mp := by
    rw [hMp]
    exact le_sup_right
  rcases h with ⟨-, -, n', hpsl, -⟩ | ⟨-, -, hpsl, -⟩ | hiii | hiii
  · exact h3 ((L2Case.three_dvd_card (Or.inl ⟨n', hpsl⟩)).trans hdvd)
  · refine h3 (dvd_trans ?_ hdvd)
    rw [SBc11.card_of_isPSL_three_two hpsl]
    norm_num
  · exact false_of_modFiveIii hW hSzE hL hσ3 hfpf hσMp hLMp
      (fun h hh => hLtMp ⟨h, hh, rfl⟩) htMp1 htMp2 hiii
  · have hL' : IsSz n ↥(conjAutSub t L) :=
      isSz_congr (L.equivMapOfInjective _ (MulAut.conj t).injective) hL
    refine false_of_modFiveIii hW hSzE hL' hσ3 hfpf hσMp hLtMp ?_
      (fun m hm => by simpa using htMp2 m hm) (fun m hm => by simpa using htMp1 m hm) hiii
    rintro _ ⟨h, hh, rfl⟩
    have e : t⁻¹ * (MulAut.conj t).toMonoidHom h * t⁻¹⁻¹ = h := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      group
    rw [e]
    exact hLMp hh

end SzMod

end CFSG.Quasithin.H13.A6
