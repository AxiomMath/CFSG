module

public import CFSG.RankThree.PartTwo.Sec21.Item2110Res3ProofAL
import CFSG.RankThree.PartTwo.Sec21.Item219LieProofD4Comm
import CFSG.RankThree.PartTwo.Sec21.Item219LieProofD4Cent
import CFSG.RankThree.PartTwo.Sec21.Item219LieProofALStar
import CFSG.RankThree.PartOne.S11.SecTenEight

public section

namespace CFSG.RankThree.PartTwo.Sec21.Item219LieProof

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo Subgroup

theorem commutator_mem_iOf218 {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (hL : IsQuasisimple ↥L) {d : G} (hdL : d ∈ L) (hd3 : d ^ 3 = 1)
    (hcomm : ∀ a ∈ centralizer ({((⟨d, hdL⟩ : L) : lBar L)} : Set (lBar L)),
      ∀ b ∈ centralizer ({((⟨d, hdL⟩ : L) : lBar L)} : Set (lBar L)),
        a * b * a⁻¹ * b⁻¹ ∈
          inSubgroup CFSG.layer (centralizer ({((⟨d, hdL⟩ : L) : lBar L)} : Set (lBar L))))
    {g b : G} (hg : g ∈ L ⊓ centralizer ({d} : Set G)) (hb : b ∈ L ⊓ centralizer ({d} : Set G))
    (hy3 : (g * b * g⁻¹ * b⁻¹) ^ 3 = 1) : g * b * g⁻¹ * b⁻¹ ∈ iOf218 L d := by
  set θ := aschbacherSolvableCore 3 ↥L with hθ
  have hθZ : θ ≤ center ↥L := PartOne.theta_le_center_of_quasisimple Nat.prime_three hL
  obtain ⟨-, -, hθ3, -⟩ := solvable_prime_complement_core_characterization (H := ↥L)
    Nat.prime_three
  set x : lBar L := ((⟨d, hdL⟩ : L) : lBar L) with hx
  set K := L ⊓ centralizer ({d} : Set G) with hK
  set Kb := centralizer ({x} : Set (lBar L)) with hKb
  set ψ₀ : ↥K →* lBar L := (QuotientGroup.mk' θ).comp (inclusion (inf_le_left : K ≤ L))
    with hψ₀
  have hrange : ψ₀.range = Kb := Item21Res7Proof.range_eq_centralizer hθZ hdL hd3
  have hmemKb : ∀ k : ↥K, ψ₀ k ∈ Kb := fun k => hrange ▸ ⟨k, rfl⟩
  set ψ : ↥K →* ↥Kb := ψ₀.codRestrict Kb hmemKb with hψ
  have hψs : Function.Surjective ψ := by
    rintro ⟨q, hq⟩
    rw [← hrange] at hq
    obtain ⟨k, hk⟩ := hq
    exact ⟨k, Subtype.ext hk⟩
  have hψker : ∀ k : ↥K, k ∈ ψ.ker ↔ inclusion (inf_le_left : K ≤ L) k ∈ θ := by
    intro k
    rw [MonoidHom.mem_ker, ← QuotientGroup.eq_one_iff]
    constructor
    · intro h
      exact congrArg Subtype.val h
    · intro h
      exact Subtype.ext h
  have hkerZ : ψ.ker ≤ center ↥K := by
    intro k hk
    rw [mem_center_iff]
    intro k'
    have h1 := mem_center_iff.mp (hθZ ((hψker k).mp hk)) (inclusion inf_le_left k')
    apply Subtype.ext
    have h2 := congrArg Subtype.val h1
    simpa using h2
  have hord : ∀ k ∈ ψ.ker, ¬ 3 ∣ orderOf k := by
    intro k hk h3
    have h1 : orderOf (⟨_, (hψker k).mp hk⟩ : θ) ∣ Nat.card θ := orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk, orderOf_injective _ (inclusion_injective inf_le_left)] at h1
    exact hθ3 (h3.trans h1)
  have hlayer := Item21Res7Proof.map_layer_of_surjective ψ hψs hkerZ
  set g₀ : ↥K := ⟨g, hg⟩ with hg₀
  set b₀ : ↥K := ⟨b, hb⟩ with hb₀
  set y₀ : ↥K := g₀ * b₀ * g₀⁻¹ * b₀⁻¹ with hy₀
  have hψy : ψ y₀ ∈ CFSG.layer ↥Kb := by
    obtain ⟨q, hq, hqe⟩ := hcomm _ (hmemKb g₀) _ (hmemKb b₀)
    have hqy : q = ψ y₀ := by
      apply Subtype.ext
      rw [show ((ψ y₀ : ↥Kb) : lBar L) = ψ₀ y₀ from rfl, hy₀, map_mul, map_mul, map_mul, map_inv,
        map_inv]
      exact hqe
    rw [← hqy]
    exact hq
  rw [← hlayer] at hψy
  obtain ⟨k, hk, hky⟩ := hψy
  have hker : k⁻¹ * y₀ ∈ ψ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hky, inv_mul_cancel]
  have hy₀3 : y₀ ^ 3 = 1 := Subtype.ext (by simpa [hy₀, hg₀, hb₀] using hy3)
  have hmem := Item21Res7Proof.mem_of_eq_mul_central hy₀3
    (fun g => (mem_center_iff.mp (hkerZ hker) g)) (hord _ hker) hk (by group)
  exact ⟨y₀, hmem, rfl⟩

theorem kF2110ALInID4_of
    (h211 : Item211) (h213 : Item213) (h45 : Sec4.Item4_5) : KF2110ALInID4 := by
  intro G _ _ A E U c L hpair ⟨n, hn, hev, hD⟩ ⟨eS⟩ d hdA hd1 hdcen
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hL : IsList218 L := Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨n, hD⟩)))))
  have hLq : IsQuasisimple ↥L := h213 G A E U c L hpair
  have hdL : d ∈ L := Item2113Proof.mem_of_isCentral218 hdcen
  have hAe := hpair.mem_S.1.1
  have hd3 : d ^ 3 = 1 := hAe.2 d hdA
  obtain ⟨hcA, -, hLc, -, hcL⟩ := Item2113Res2Proof.pair_data h45 hpair hL
  have h27 : Nat.card A = 27 := by
    rw [Item2113Proof.card_eq_of_isList218 h211 hpair hL]; norm_num
  have h9 : Nat.card (A ⊓ L : Subgroup G) = 9 :=
    Item2113Res3Proof.card_inf_eq_nine h211 h45 hpair hL
  have hxc := Item21Res7Proof.isCentral_lBar hdL hdcen
  have hx1 : ((⟨d, hdL⟩ : L) : lBar L) ≠ 1 := by
    intro h1
    rw [QuotientGroup.eq_one_iff] at h1
    obtain ⟨-, -, hθ3, -⟩ := solvable_prime_complement_core_characterization (H := ↥L)
      Nat.prime_three
    have hord : orderOf (⟨d, hdL⟩ : L) = 3 :=
      orderOf_eq_prime (Subtype.ext (by simpa using hd3)) fun h => hd1 (congrArg Subtype.val h)
    have h2 := orderOf_dvd_natCard (⟨_, h1⟩ : aschbacherSolvableCore 3 ↥L)
    rw [Subgroup.orderOf_mk, hord] at h2
    exact hθ3 h2
  have hdI : d ∈ iOf218 L d := (Item21Res7Proof.iOf218_transport hLq hdL hd3).1
    (ks219D4_holds (lBar L) n hn hev hD _ hx1 hxc).1
  have hcommI : ∀ {g b : G}, g ∈ L ⊓ centralizer ({d} : Set G) →
      b ∈ L ⊓ centralizer ({d} : Set G) → (g * b * g⁻¹ * b⁻¹) ^ 3 = 1 →
        g * b * g⁻¹ * b⁻¹ ∈ iOf218 L d := fun hg hb hy3 =>
    commutator_mem_iOf218 hLq hdL hd3 (ks219D4_commutator_mem (lBar L) n hn hev hD _ hx1 hxc)
      hg hb hy3
  set B : Subgroup A := (A ⊓ L).subgroupOf A with hB
  have hB9 : Nat.card B = 9 := by rw [hB, Item2113Res2Proof.card_inf_subgroupOf, h9]
  have hSB : ∀ σ ∈ starOf A L, ∀ x ∈ B, σ x ∈ B := by
    rintro _ ⟨w, hwL, rfl⟩ x hx
    rw [Item2113Res2Proof.mem_inf_subgroupOf] at hx ⊢
    rw [normalizerMonoidHom_apply_apply_coe]
    exact L.mul_mem (L.mul_mem (mem_subgroupOf.mp hwL) hx) (L.inv_mem (mem_subgroupOf.mp hwL))
  have hfaith : ∀ σ ∈ starOf A L, (∀ x ∈ B, σ x = x) → σ = 1 := by
    intro σ hσ hfix
    have hσc : σ ⟨c, hcA⟩ = ⟨c, hcA⟩ := Item2113Res2Proof.apply_eq_of_mem_starOf hcA hLc hσ
    set F : Subgroup A := σ.toMonoidHom.eqLocus (MonoidHom.id A) with hF
    have hBF : B ≤ F := fun x hx => hfix x hx
    have hcF : (⟨c, hcA⟩ : A) ∈ F := hσc
    have hcB : (⟨c, hcA⟩ : A) ∉ B := fun h => hcL (Item2113Res2Proof.mem_inf_subgroupOf.mp h)
    have hlt : B < F := lt_of_le_of_ne hBF fun h => hcB (h ▸ hcF)
    have hdvd : Nat.card F ∣ 27 := h27 ▸ card_subgroup_dvd_card F
    have hgt : 9 < Nat.card F := hB9 ▸ card_lt_of_lt hlt
    have hF27 : Nat.card F = 27 := by
      have hle : Nat.card F ≤ 27 := Nat.le_of_dvd (by norm_num) hdvd
      interval_cases h : Nat.card F <;> omega
    have hFtop : F = ⊤ := eq_top_of_card_eq F (by rw [hF27, h27])
    refine MulEquiv.ext fun x => ?_
    have hx : x ∈ F := hFtop ▸ mem_top x
    exact hx
  set d₀ : A := ⟨d, hdA⟩ with hd₀
  have hd₀B : d₀ ∈ B := Item2113Res2Proof.mem_inf_subgroupOf.mpr hdL
  have hd₀1 : d₀ ≠ 1 := fun h => hd1 (congrArg Subtype.val h)
  obtain ⟨σ, hσS, hσd, hσ2, hσ1⟩ := exists_involution_fix eS hB9 hSB hfaith hd₀B hd₀1
  obtain ⟨b, hbB, hbσ⟩ : ∃ b ∈ B, σ b ≠ b := by
    by_contra h
    push Not at h
    exact hσ1 (hfaith σ hσS h)
  have hσσ : σ (σ b) = b := by
    have h1 : (σ * σ) b = b := by rw [← pow_two, hσ2]; rfl
    exact h1
  obtain ⟨w, hwL, rfl⟩ := hσS
  have hwL' : (w : G) ∈ L := mem_subgroupOf.mp hwL
  have hwd : (w : G) * d = d * (w : G) := by
    have h1 := congrArg Subtype.val hσd
    rw [normalizerMonoidHom_apply_apply_coe] at h1
    calc (w : G) * d = (w : G) * d * (w : G)⁻¹ * (w : G) := by group
      _ = d * (w : G) := by rw [h1]
  set y₀ : A := A.normalizerMonoidHom w b * b⁻¹ with hy₀
  have hy₀G : (y₀ : G) = (w : G) * (b : G) * (w : G)⁻¹ * (b : G)⁻¹ := by
    rw [hy₀, Subgroup.coe_mul, normalizerMonoidHom_apply_apply_coe, Subgroup.coe_inv]
  have hbL : (b : G) ∈ L := Item2113Res2Proof.mem_inf_subgroupOf.mp hbB
  have hbd : (b : G) * d = d * (b : G) :=
    congrArg Subtype.val (hAe.1.is_comm.comm b d₀)
  have hy3 : ((w : G) * (b : G) * (w : G)⁻¹ * (b : G)⁻¹) ^ 3 = 1 := by
    rw [← hy₀G]
    exact hAe.2 _ y₀.2
  have hyI : (y₀ : G) ∈ iOf218 L d := by
    rw [hy₀G]
    exact hcommI ⟨hwL', mem_centralizer_singleton_iff.mpr hwd⟩
      ⟨hbL, mem_centralizer_singleton_iff.mpr hbd⟩ hy3
  have hσy : A.normalizerMonoidHom w y₀ = y₀⁻¹ := by
    rw [hy₀, map_mul, map_inv, hσσ]
    group
  have hy₀3 : y₀ ^ 3 = 1 := Subtype.ext (hAe.2 _ y₀.2)
  have hyd : (y₀ : G) ∉ zpowers d := by
    intro h
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp h
    have hk' : d₀ ^ k = y₀ := Subtype.ext (by rw [Subgroup.coe_zpow]; exact hk)
    have h1 : A.normalizerMonoidHom w y₀ = y₀ := by rw [← hk', map_zpow, hσd]
    rw [h1] at hσy
    have h2 : y₀ ^ 2 = 1 := by
      rw [pow_two]
      nth_rewrite 2 [hσy]
      exact mul_inv_cancel y₀
    have h3 : y₀ = 1 := by
      calc y₀ = y₀ ^ 3 * (y₀ ^ 2)⁻¹ := by group
        _ = 1 := by rw [hy₀3, h2]; group
    apply hbσ
    rw [hy₀, mul_inv_eq_one] at h3
    exact h3
  have hyAL : (y₀ : G) ∈ A ⊓ L := by
    refine ⟨y₀.2, ?_⟩
    rw [hy₀G]
    exact L.mul_mem (L.mul_mem (L.mul_mem hwL' hbL) (L.inv_mem hwL')) (L.inv_mem hbL)
  set D := zpowers d ⊔ zpowers (y₀ : G) with hD
  have hDle : D ≤ A ⊓ L := sup_le (zpowers_le.mpr ⟨hdA, hdL⟩) (zpowers_le.mpr hyAL)
  have hcard3 : Nat.card (zpowers d) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime hd3 hd1]
  have hlt : zpowers d < D :=
    lt_of_le_of_ne le_sup_left fun h => hyd (h ▸ mem_sup_right (mem_zpowers _))
  have hD9 : Nat.card D = 9 := by
    have hdvd : Nat.card D ∣ 9 := h9 ▸ card_dvd_of_le hDle
    have hgt : 3 < Nat.card D := hcard3 ▸ card_lt_of_lt hlt
    have hle : Nat.card D ≤ 9 := Nat.le_of_dvd (by norm_num) hdvd
    interval_cases h : Nat.card D <;> omega
  have hDeq : D = A ⊓ L := eq_of_le_of_card_ge hDle (by rw [hD9, h9])
  rw [← hDeq]
  exact sup_le (zpowers_le.mpr hdI) (zpowers_le.mpr hyI)

end CFSG.RankThree.PartTwo.Sec21.Item219LieProof
