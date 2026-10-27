module

public import CFSG.RankThree.GF2n.Tim79a34GriessSpException
import CFSG.GroupTheory.CentralSplitTransfer
import CFSG.GroupTheory.CentralExtensionPerfectPreimage
import CFSG.GH74.GLS.C3.Prop121.A7Cover

public section

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG.Open Subgroup
open scoped commutatorElement

theorem card_ker_dvd_six_perm_six {Γ : Type} [Group Γ] [Finite Γ]
    (φ : Γ →* Equiv.Perm (Fin 6)) (hφ : Function.Surjective φ)
    (hcen : φ.ker ≤ Subgroup.center Γ) (hcom : φ.ker ≤ commutator Γ) :
    Nat.card φ.ker ∣ 6 := by
  have hperfA : Group.IsPerfect ↥(alternatingGroup (Fin 6)) :=
    CFSG.Holt.H78.isPerfect_alternatingGroup (by norm_num)
  have hL : ⁅(alternatingGroup (Fin 6) : Subgroup (Equiv.Perm (Fin 6))),
      alternatingGroup (Fin 6)⁆ = alternatingGroup (Fin 6) :=
    Subgroup.isPerfect_iff.mp hperfA
  haveI hcyc : IsCyclic (Equiv.Perm (Fin 6) ⧸ alternatingGroup (Fin 6)) :=
    isCyclic_of_prime_card (alternatingGroup.index_eq_two (α := Fin 6))
  haveI : Group.IsPerfect ↥((alternatingGroup (Fin 6)).comap φ) :=
    CFSG.GroupTheory.isPerfect_comap_of_isCyclic_quotient φ hφ hcen hcom hL
  let Γ₀ : Subgroup Γ := (alternatingGroup (Fin 6)).comap φ
  let φ₀ : ↥Γ₀ →* ↥(alternatingGroup (Fin 6)) :=
    (φ.comp Γ₀.subtype).codRestrict _ fun x => x.2
  have hφ₀ : Function.Surjective φ₀ := by
    rintro ⟨y, hy⟩
    obtain ⟨x, hx⟩ := hφ y
    refine ⟨⟨x, ?_⟩, Subtype.ext hx⟩
    show φ x ∈ alternatingGroup (Fin 6)
    rw [hx]
    exact hy
  have hKle : φ.ker ≤ Γ₀ := by
    intro x hx
    show φ x ∈ alternatingGroup (Fin 6)
    rw [MonoidHom.mem_ker] at hx
    rw [hx]
    exact (alternatingGroup (Fin 6)).one_mem
  have hker : Nat.card φ₀.ker = Nat.card φ.ker := by
    have hEq : φ₀.ker = φ.ker.subgroupOf Γ₀ := by
      ext x
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, MonoidHom.mem_ker]
      exact Subtype.ext_iff
    rw [hEq]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKle).toEquiv
  have hcen' : φ₀.ker ≤ Subgroup.center ↥Γ₀ := by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    have hx1 : φ (x : Γ) = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
    exact Subgroup.mem_center_iff.mp (hcen hx1) (y : Γ)
  have hsurj := CFSG.RankThree.PerfectCover.hopfMultiplierToKer_surjective φ₀ hφ₀ hcen'
  have hcard := CFSG.RankThree.PerfectCover.card_eq_card_mul_card_ker
    (CFSG.RankThree.PerfectCover.hopfMultiplierToKer φ₀ hφ₀ hcen') hsurj
  have h6 : Nat.card
      (CFSG.RankThree.PerfectCover.hopfMultiplier ↥(alternatingGroup (Fin 6))) = 6 :=
    (CFSG.Alternating.Multipliers.hopfMultiplier_alternatingGroup_six).2
  rw [h6, hker] at hcard
  exact ⟨_, hcard⟩

theorem card_closure_threeCycles :
    Nat.card ↥(Subgroup.closure ({c[0, 1, 2], c[3, 4, 5]} : Set (Equiv.Perm (Fin 6)))) = 9 := by
  have ha3 : (c[0, 1, 2] : Equiv.Perm (Fin 6)) ^ 3 = 1 := by decide
  have hb3 : (c[3, 4, 5] : Equiv.Perm (Fin 6)) ^ 3 = 1 := by decide
  have hab : (c[0, 1, 2] : Equiv.Perm (Fin 6)) * c[3, 4, 5] = c[3, 4, 5] * c[0, 1, 2] := by
    decide
  haveI hCc : IsMulCommutative ↥(Subgroup.closure
      ({c[0, 1, 2], c[3, 4, 5]} : Set (Equiv.Perm (Fin 6)))) :=
    Subgroup.isMulCommutative_closure (by
      intro u hu v hv _
      rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hu hv
      rcases hu with rfl | rfl <;> rcases hv with rfl | rfl <;>
        first | exact hab | exact hab.symm | rfl)
  have hexp : ∀ z ∈ Subgroup.closure ({c[0, 1, 2], c[3, 4, 5]} : Set (Equiv.Perm (Fin 6))),
      z ^ 3 = 1 := by
    intro z hz
    induction hz using Subgroup.closure_induction with
    | mem x hx =>
        rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        rcases hx with rfl | rfl <;> assumption
    | one => exact one_pow 3
    | mul x y hx hy ihx ihy =>
        have hc : Commute x y :=
          Subgroup.mul_comm_of_mem_isMulCommutative
            (H := Subgroup.closure ({c[0, 1, 2], c[3, 4, 5]} : Set (Equiv.Perm (Fin 6)))) hx hy
        rw [hc.mul_pow, ihx, ihy, one_mul]
    | inv x hx ih => rw [inv_pow, ih, inv_one]
  have hP : IsPGroup 3 ↥(Subgroup.closure
      ({c[0, 1, 2], c[3, 4, 5]} : Set (Equiv.Perm (Fin 6)))) :=
    fun z => ⟨1, by
      apply Subtype.ext
      simpa using hexp (z : Equiv.Perm (Fin 6)) z.2⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 3)).mp hP
  have hdvd : 3 ^ k ∣ 720 := by
    rw [← hk]
    have h := Subgroup.card_subgroup_dvd_card
      (Subgroup.closure ({c[0, 1, 2], c[3, 4, 5]} : Set (Equiv.Perm (Fin 6))))
    rwa [Nat.card_perm, Nat.card_fin, show Nat.factorial 6 = 720 by decide] at h
  have hcop : Nat.Coprime (3 ^ k) 80 := (by norm_num : Nat.Coprime 3 80).pow_left k
  have h9 : 3 ^ k ∣ 9 := hcop.dvd_of_dvd_mul_right (by simpa using hdvd)
  have hk2 : k ≤ 2 := (Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 3)).mp (by simpa using h9)
  have hle9 : 3 ^ k ≤ 9 := by
    simpa using Nat.pow_le_pow_right (by norm_num : 0 < 3) hk2
  have hge9 : 9 ≤ Nat.card ↥(Subgroup.closure
      ({c[0, 1, 2], c[3, 4, 5]} : Set (Equiv.Perm (Fin 6)))) := by
    let f : Fin 3 × Fin 3 → ↥(Subgroup.closure
        ({c[0, 1, 2], c[3, 4, 5]} : Set (Equiv.Perm (Fin 6)))) :=
      fun p => ⟨(c[0, 1, 2]) ^ (p.1 : ℕ) * (c[3, 4, 5]) ^ (p.2 : ℕ),
        Subgroup.mul_mem _ (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _)
          (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _)⟩
    have hinj : Function.Injective f := by decide
    simpa [Nat.card_prod] using Nat.card_le_card_of_injective f hinj
  omega

theorem index_comap_closure_threeCycles {Γ : Type} [Group Γ] (φ : Γ →* Equiv.Perm (Fin 6))
    (hφ : Function.Surjective φ) :
    ((Subgroup.closure ({c[0, 1, 2], c[3, 4, 5]} : Set (Equiv.Perm (Fin 6)))).comap φ).index =
      80 := by
  rw [Subgroup.index_comap_of_surjective
    (Subgroup.closure ({c[0, 1, 2], c[3, 4, 5]} : Set (Equiv.Perm (Fin 6)))) hφ]
  have h := Subgroup.index_mul_card
    (Subgroup.closure ({c[0, 1, 2], c[3, 4, 5]} : Set (Equiv.Perm (Fin 6))))
  rw [card_closure_threeCycles, Nat.card_perm, Nat.card_fin,
    show Nat.factorial 6 = 720 by decide] at h
  omega

theorem not_three_dvd_card_ker_perm_six {Γ : Type} [Group Γ] [Finite Γ]
    (φ : Γ →* Equiv.Perm (Fin 6)) (hφ : Function.Surjective φ)
    (hcen : φ.ker ≤ Subgroup.center Γ) (hcom : φ.ker ≤ commutator Γ) :
    ¬ 3 ∣ Nat.card φ.ker := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  intro h3
  have ha3 : (c[0, 1, 2] : Equiv.Perm (Fin 6)) ^ 3 = 1 := by decide
  have hab : (c[0, 1, 2] : Equiv.Perm (Fin 6)) * c[3, 4, 5] = c[3, 4, 5] * c[0, 1, 2] := by
    decide
  have hta : (Equiv.swap 0 1 : Equiv.Perm (Fin 6)) * c[0, 1, 2] * (Equiv.swap 0 1)⁻¹ =
      (c[0, 1, 2])⁻¹ := by decide
  have htb : (Equiv.swap 0 1 : Equiv.Perm (Fin 6)) * c[3, 4, 5] * (Equiv.swap 0 1)⁻¹ =
      c[3, 4, 5] := by decide
  obtain ⟨a', ha'⟩ := hφ (c[0, 1, 2])
  obtain ⟨b', hb'⟩ := hφ (c[3, 4, 5])
  obtain ⟨t', ht'⟩ := hφ (Equiv.swap 0 1)
  have hhab : Commute (φ a') (φ b') := by rw [ha', hb']; exact hab
  have hha : φ a' ^ 3 = 1 := by rw [ha']; exact ha3
  have hhta : φ t' * φ a' * (φ t')⁻¹ = (φ a')⁻¹ := by rw [ha', ht']; exact hta
  have hhtb : φ t' * φ b' * (φ t')⁻¹ = φ b' := by rw [hb', ht']; exact htb
  have hcomm' : Commute a' b' :=
    CFSG.GroupTheory.commute_of_commute_map_of_conj_inv φ hcen ⟨1, rfl⟩ hhab hha hhta hhtb
  set H : Subgroup Γ := (Subgroup.closure ({φ a', φ b'} : Set (Equiv.Perm (Fin 6)))).comap φ with hH
  have hHpoint : ∀ p ∈ H, ∀ q ∈ H, p * q = q * p :=
    CFSG.GH74.GLS.C3.Prop121.preimage_closure_pair_commutes_of_commute φ hcen hcomm'
      (by rw [ha', hb']; exact hab)
  have hbot : ⁅H, H⁆ = ⊥ :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mpr fun p hp =>
      Subgroup.mem_centralizer_iff.mpr fun q hq => (hHpoint p hp q hq).symm
  have hidx : H.index = 80 := by
    rw [hH, show ({φ a', φ b'} : Set (Equiv.Perm (Fin 6))) = {c[0, 1, 2], c[3, 4, 5]} by
      rw [ha', hb']]
    exact index_comap_closure_threeCycles φ hφ
  have h3idx : ¬ 3 ∣ H.index := by rw [hidx]; norm_num
  obtain ⟨g, hgK, hgord⟩ : ∃ g : Γ, g ∈ φ.ker ∧ orderOf g = 3 := by
    obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := ↥φ.ker) 3 h3
    exact ⟨(g : Γ), g.2, by rw [Subgroup.orderOf_coe]; exact hg⟩
  have hgZ : g ∈ Subgroup.center Γ := hcen hgK
  have hKleH : φ.ker ≤ H := by rw [hH]; exact MonoidHom.ker_le_comap φ _
  have hgne : g ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hgord
    exact absurd hgord (by norm_num)
  have hgnot : g ∉ ⁅H, H⁆ := by rw [hbot]; simpa using hgne
  refine CFSG.GroupTheory.not_mem_commutator_of_relIndex (C := ⊤) (H := H) (p := 3)
    le_top ?_ (hKleH hgK) (fun x _ => (Subgroup.mem_center_iff.mp hgZ x).symm) hgord hgnot ?_
  · rw [Subgroup.relIndex_top_right]
    exact h3idx
  · exact hcom hgK

theorem card_ker_le_two_perm_six {Γ : Type} [Group Γ] [Finite Γ]
    (φ : Γ →* Equiv.Perm (Fin 6)) (hφ : Function.Surjective φ)
    (hcen : φ.ker ≤ Subgroup.center Γ) (hcom : φ.ker ≤ commutator Γ) :
    Nat.card φ.ker ≤ 2 := by
  have h1 : Nat.card φ.ker ∣ 6 := card_ker_dvd_six_perm_six φ hφ hcen hcom
  have h2 : ¬ 3 ∣ Nat.card φ.ker := not_three_dvd_card_ker_perm_six φ hφ hcen hcom
  have hcop : Nat.Coprime (Nat.card φ.ker) 3 :=
    ((Nat.prime_three.coprime_iff_not_dvd).mpr h2).symm
  have hdvd : Nat.card φ.ker ∣ 2 := hcop.dvd_of_dvd_mul_right (by simpa using h1)
  exact Nat.le_of_dvd (by norm_num) hdvd

theorem card_ker_le_two_statedSp_two_one {Γ : Type} [Group Γ]
    [Finite Γ] (φ : Γ →* StatedSp 2 (GaloisField 2 1)) (hφ : Function.Surjective φ)
    (hcen : φ.ker ≤ Subgroup.center Γ) (hcom : φ.ker ≤ commutator Γ) :
    Nat.card φ.ker ≤ 2 := by
  have hF2 : Nat.card (GaloisField 2 1) = 2 := by
    rw [GaloisField.card 2 1 one_ne_zero, pow_one]
  let e : StatedSp 2 (GaloisField 2 1) ≃* Equiv.Perm (Fin 6) :=
    (CFSG.SignalizerFunctorTheorem.NonLocal.spTwoTwoEquiv hF2).trans
      CFSG.Quasithin.H13.Sp4Cert.sympFourEquiv
  let ψ : Γ →* Equiv.Perm (Fin 6) := e.toMonoidHom.comp φ
  have hψ : Function.Surjective ψ := e.surjective.comp hφ
  have hker : ψ.ker = φ.ker := by
    ext x
    simp only [ψ, MonoidHom.mem_ker, MonoidHom.comp_apply]
    exact e.map_eq_one_iff
  have hcen' : ψ.ker ≤ Subgroup.center Γ := hker ▸ hcen
  have hcom' : ψ.ker ≤ commutator Γ := hker ▸ hcom
  have := card_ker_le_two_perm_six ψ hψ hcen' hcom'
  rwa [hker] at this

theorem griessSpMultiplierExceptionStatement_holds :
    CFSG.RankThree.GF2n.Tim79a.GriessSpMultiplierExceptionStatement :=
  griessSpMultiplierExceptionStatement_of_s6_upper
    (fun Γ _ _ φ hφ hcen hcom => card_ker_le_two_statedSp_two_one φ hφ hcen hcom)

end CFSG.RankThree.GF2n.Tim79a
