module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm13_10.Basic
public import CFSG.CharacterTheory.Semidihedral.Principal.CyclicInversionAlternatingFive
public import CFSG.LocalAnalysis.UniquenessCase.UCFront09R93a
public import CFSG.Sporadic.Co2Cert.Order

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm13_10

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.Quasithin.F6
open CFSG.LocalAnalysis.WeakClosure81

open CFSG.Blueprint (LieModel)
open scoped commutatorElement Pointwise

theorem perm_pow_five : ∀ s : Equiv.Perm (Fin 5), s ^ 25 = 1 →
    s ^ 5 = 1 ∧ s ∈ alternatingGroup (Fin 5) := by
  decide +kernel

theorem exists_inner_of_pow_five {G : Type} [Group G] {L : Subgroup G} (hL : IsAlt ↥L 5)
    {y : G} (hyL : y ∈ Subgroup.normalizer (L : Set G)) {k : ℕ} (hy : y ^ (5 ^ k) = 1) :
    ∃ a ∈ L, a ^ 5 = 1 ∧ ∀ x ∈ L, y * x * y⁻¹ = a * x * a⁻¹ := by
  obtain ⟨e⟩ := hL
  set E := CFSG.Semidihedral.Principal.CyclicAlternatingFive.autEquiv with hE
  set σ : MulAut ↥L := L.normalizerMonoidHom ⟨y, hyL⟩ with hσ
  have hσapp : ∀ x : ↥L, ((σ x : ↥L) : G) = y * (x : G) * y⁻¹ := fun x =>
    Subgroup.normalizerMonoidHom_apply_apply_coe L ⟨y, hyL⟩ x
  have hybar : (⟨y, hyL⟩ : ↥(Subgroup.normalizer (L : Set G))) ^ (5 ^ k) = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow]
    simpa using hy
  have hσpow : σ ^ (5 ^ k) = 1 := by
    rw [hσ, ← map_pow, hybar, map_one]
  set α : MulAut (alternatingGroup (Fin 5)) := MulAut.congr e σ with hα
  have hαpow : α ^ (5 ^ k) = 1 := by
    rw [hα, ← map_pow, hσpow, map_one]
  set s : Equiv.Perm (Fin 5) := E.symm α with hs
  have hEs : E s = α := by rw [hs, MulEquiv.apply_symm_apply]
  have hspow : s ^ (5 ^ k) = 1 := by
    apply E.injective
    rw [map_pow, hEs, hαpow, map_one]
  have hs5 : s ^ 5 = 1 := by
    have aux : ∀ n, s ^ (5 ^ n) = 1 → s ^ 5 = 1 := by
      intro n
      induction n with
      | zero =>
          intro h
          rw [show s = 1 by simpa using h, one_pow]
      | succ n ih =>
          intro h
          rcases n with _ | m
          · simpa using h
          · have h25 : (s ^ (5 ^ m)) ^ 25 = 1 := by
              rw [← pow_mul, show 25 = 5 ^ 2 by norm_num, ← pow_add]
              simpa using h
            have hnext : s ^ (5 ^ (m + 1)) = 1 := by
              rw [pow_succ, pow_mul]
              exact (perm_pow_five (s ^ (5 ^ m)) h25).1
            exact ih hnext
    exact aux k hspow
  have hs25 : s ^ 25 = 1 := by
    rw [show 25 = 5 * 5 by norm_num, pow_mul, hs5, one_pow]
  have hsA : s ∈ alternatingGroup (Fin 5) := (perm_pow_five s hs25).2
  let a : ↥L := e.symm ⟨s, hsA⟩
  have hae : e a = ⟨s, hsA⟩ := e.apply_symm_apply _
  have ha5L : a ^ 5 = 1 := by
    apply e.injective
    rw [map_pow, map_one, hae]
    apply Subtype.ext
    simpa using hs5
  have hαe : ∀ z : ↥L, α (e z) = e (σ z) := by
    intro z
    rw [hα, MulAut.congr_apply]
    simp
  have happ : ∀ z : ↥L,
      ((α (e z) : alternatingGroup (Fin 5)) : Equiv.Perm (Fin 5)) =
        s * (e z : Equiv.Perm (Fin 5)) * s⁻¹ := by
    intro z
    rw [← hEs, hE,
      CFSG.Semidihedral.Principal.CyclicAlternatingFive.autEquiv_apply]
    rfl
  have hrhs : ∀ z : ↥L,
      ((e (a * z * a⁻¹) : alternatingGroup (Fin 5)) : Equiv.Perm (Fin 5)) =
        s * (e z : Equiv.Perm (Fin 5)) * s⁻¹ := by
    intro z
    rw [map_mul, map_mul, map_inv, hae]
    rfl
  have hσeq : ∀ z : ↥L, σ z = a * z * a⁻¹ := by
    intro z
    apply e.injective
    apply Subtype.ext
    rw [← hαe z, happ z, hrhs z]
  refine ⟨(a : G), a.2, ?_, ?_⟩
  · rw [← Subgroup.coe_pow, ha5L]
    rfl
  · intro x hx
    have hσx := hσapp ⟨x, hx⟩
    have h2 := congrArg (fun w : ↥L => (w : G)) (hσeq ⟨x, hx⟩)
    rw [hσx] at h2
    have h := hσx.symm.trans h2
    simpa using h

private theorem eq_one_of_pow_five_pow_eq_one {W : Type*} [CommGroup W]
    {Y X : Subgroup (MulAut W)} {c : MulAut W} (hcY : c ∈ Y)
    (hcX : ∀ z ∈ X, c * z = z * c)
    (hno5 : ∀ d ∈ Y, (∀ z ∈ X, d * z = z * d) → d ^ 5 = 1 → d = 1)
    {k : ℕ} (hk : c ^ (5 ^ k) = 1) : c = 1 := by
  have key : ∀ i, i ≤ k → c ^ (5 ^ (k - i)) = 1 := by
    intro i
    induction i with
    | zero =>
        intro _
        simpa using hk
    | succ i ih =>
        intro hi
        have hik : i ≤ k := by omega
        have hd5 : (c ^ (5 ^ (k - i - 1))) ^ 5 = 1 := by
          rw [← pow_mul]
          rw [show 5 ^ (k - i - 1) * 5 = 5 ^ (k - i) by
            rw [← pow_succ, show k - i - 1 + 1 = k - i by omega]]
          exact ih hik
        have hmain := hno5 _ (Subgroup.pow_mem Y hcY _)
          (fun z hz => (Commute.pow_left (show Commute c z from hcX z hz) _).eq) hd5
        simpa [show k - (i + 1) = k - i - 1 by omega] using hmain
  simpa using key k le_rfl

theorem opp_five_eq_sup {W : Type} [CommGroup W] [Finite W]
    {Y L K : Subgroup (MulAut W)} (hcL : IsComponentOf L Y) (hcK : IsComponentOf K Y)
    (haL : IsAlt ↥L 5) (haK : IsAlt ↥K 5) (hne : L ≠ K)
    (hXn : ((L ⊔ K).subgroupOf Y).Normal)
    (hno5 : ∀ c ∈ Y, (∀ x ∈ L ⊔ K, c * x = x * c) → c ^ 5 = 1 → c = 1) :
    Opp 5 Y = L ⊔ K := by
  have hcomm := CFSG.Quasithin.B69.components_mul_comm_of_ne hcL hcK hne
  have hM_le : ∀ {M : Subgroup (MulAut W)}, IsAlt ↥M 5 → M ≤ Y → M ≤ Opp 5 Y := by
    intro M halt hMY
    obtain ⟨e⟩ := halt
    have hcard : Nat.card ↥M = 60 := by
      rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup,
        Fintype.card_fin]
      decide
    have hdvd : 5 ∣ Nat.card ↥M := by rw [hcard]; norm_num
    obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' 5 hdvd
    have hMleOppM : M ≤ Opp 5 M := by
      haveI : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup_five
      haveI : IsSimpleGroup ↥M := MulEquiv.isSimpleGroup e
      let O : Subgroup ↥M := (Opp 5 M).subgroupOf M
      have hOn : O.Normal := CFSG.LocalAnalysis.UniquenessCase.UC22.F09.normal_opp_subgroupOf 5 M
      haveI : O.Normal := hOn
      have hgO : g ∈ O := by
        rw [Subgroup.mem_subgroupOf]
        exact Subgroup.subset_closure ⟨g.2, 1, by rw [pow_one, Subgroup.orderOf_coe]; exact hg⟩
      have hOne : O ≠ ⊥ := by
        intro hbot
        have hg1 : g = 1 := by
          rw [hbot] at hgO
          exact Subgroup.mem_bot.mp hgO
        have hone : orderOf g = 1 := by rw [hg1, orderOf_one]
        omega
      have htop : O = ⊤ := (Subgroup.Normal.eq_bot_or_eq_top O).resolve_left hOne
      intro m hm
      have hmem : (⟨m, hm⟩ : ↥M) ∈ O := by rw [htop]; exact Subgroup.mem_top _
      exact Subgroup.mem_subgroupOf.mp hmem
    have hmono : Opp 5 M ≤ Opp 5 Y := by
      rw [CFSG.LocalAnalysis.UniquenessCase.UC22.Opp,
        CFSG.RankThree.PartOne.pElementSubgroup,
        CFSG.LocalAnalysis.UniquenessCase.UC22.Opp,
        CFSG.RankThree.PartOne.pElementSubgroup]
      exact Subgroup.closure_mono fun x hx => ⟨hMY hx.1, hx.2⟩
    exact hMleOppM.trans hmono
  apply le_antisymm
  · rw [CFSG.LocalAnalysis.UniquenessCase.UC22.Opp,
      CFSG.RankThree.PartOne.pElementSubgroup]
    refine (Subgroup.closure_le (L ⊔ K)).mpr ?_
    rintro x ⟨hxY, k, hk⟩
    have hxpow : x ^ (5 ^ k) = 1 := by simpa [hk] using pow_orderOf_eq_one x
    have hfix : (L.map (MulAut.conj x).toMonoidHom = L ∧
        K.map (MulAut.conj x).toMonoidHom = K) := by
      rcases map_conj_cases hcL hcK hne hXn hxY with h | h
      · exact h
      · exfalso
        obtain ⟨hLK, hKL⟩ := h
        have hx2norm : x ^ 2 ∈ Subgroup.normalizer (L : Set (MulAut W)) := by
          rw [Subgroup.mem_normalizer_iff_map_conj_eq]
          have h := CFSG.Quasithin.B19.map_conj_map_conj L x x
          rw [show x * x = x ^ 2 from (pow_two x).symm] at h
          rw [hLK, hKL] at h
          exact h.symm
        have hodd : Odd (5 ^ k) := Odd.pow (by norm_num : Odd 5)
        obtain ⟨m, hm⟩ := hodd
        have hx_eq : x = (x ^ 2) ^ (m + 1) := by
          rw [← pow_mul]
          have h2 : 2 * (m + 1) = 5 ^ k + 1 := by omega
          rw [h2, pow_succ, hxpow, one_mul]
        have hxnorm : x ∈ Subgroup.normalizer (L : Set (MulAut W)) := by
          rw [hx_eq]
          exact Subgroup.pow_mem _ hx2norm (m + 1)
        have hLfix : L.map (MulAut.conj x).toMonoidHom = L :=
          Subgroup.mem_normalizer_iff_map_conj_eq.mp hxnorm
        rw [hLfix] at hLK
        exact hne hLK
    obtain ⟨hLfix, hKfix⟩ := hfix
    have hxLnorm : x ∈ Subgroup.normalizer (L : Set (MulAut W)) :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mpr hLfix
    have hxKnorm : x ∈ Subgroup.normalizer (K : Set (MulAut W)) :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mpr hKfix
    rcases k with _ | k
    · have hx1 : x = 1 := by simpa using hxpow
      rw [hx1]
      exact (L ⊔ K).one_mem
    · obtain ⟨a, haL, ha5, hainner⟩ :=
        exists_inner_of_pow_five (G := MulAut W) (L := L) haL hxLnorm hxpow
      obtain ⟨b, hbK, hb5, hbinner⟩ :=
        exists_inner_of_pow_five (G := MulAut W) (L := K) haK hxKnorm hxpow
      have hxa : x * a = a * x := by
        have h' : x * a * x⁻¹ = a := by
          rw [hainner a haL]
          group
        calc x * a = (x * a * x⁻¹) * x := by group
          _ = a * x := by rw [h']
      have hxb : x * b = b * x := by
        have h' : x * b * x⁻¹ = b := by
          rw [hbinner b hbK]
          group
        calc x * b = (x * b * x⁻¹) * x := by group
          _ = b * x := by rw [h']
      let c : MulAut W := x * (a * b)⁻¹
      have habX : a * b ∈ L ⊔ K :=
        (L ⊔ K).mul_mem (Subgroup.mem_sup_left haL) (Subgroup.mem_sup_right hbK)
      have habY : a * b ∈ Y := (sup_le hcL.1 hcK.1) habX
      have hcY : c ∈ Y := Y.mul_mem hxY (Y.inv_mem habY)
      have hxabin : x * (a * b) = (a * b) * x := by
        calc x * (a * b) = (x * a) * b := (mul_assoc _ _ _).symm
          _ = (a * x) * b := by rw [hxa]
          _ = a * (x * b) := mul_assoc _ _ _
          _ = a * (b * x) := by rw [hxb]
          _ = (a * b) * x := (mul_assoc _ _ _).symm
      have hxabinv : x * (a * b)⁻¹ = (a * b)⁻¹ * x :=
        (Commute.inv_right (show Commute x (a * b) from hxabin)).eq
      have hczL : ∀ z ∈ L, c * z = z * c := by
        intro z hz
        have hwL : a⁻¹ * z * a ∈ L := L.mul_mem (L.mul_mem (L.inv_mem haL) hz) haL
        have hbw : b * (a⁻¹ * z * a) = (a⁻¹ * z * a) * b := hcomm b hbK _ hwL
        have hconj1 : (a * b)⁻¹ * z * (a * b) = a⁻¹ * z * a := by
          rw [mul_inv_rev]
          calc b⁻¹ * a⁻¹ * z * (a * b) = b⁻¹ * (a⁻¹ * z * a) * b := by group
            _ = b⁻¹ * ((a⁻¹ * z * a) * b) := by group
            _ = b⁻¹ * (b * (a⁻¹ * z * a)) := by rw [← hbw]
            _ = a⁻¹ * z * a := by group
        have hxconj := hainner _ hwL
        have hxconj' : x * (a⁻¹ * z * a) * x⁻¹ = z := by
          rw [hxconj]
          group
        have hcz : c * z * c⁻¹ = z := by
          calc c * z * c⁻¹ = x * ((a * b)⁻¹ * z * (a * b)) * x⁻¹ := by
                simp only [c]
                group
            _ = x * (a⁻¹ * z * a) * x⁻¹ := by rw [hconj1]
            _ = z := hxconj'
        calc c * z = (c * z * c⁻¹) * c := by group
          _ = z * c := by rw [hcz]
      have hczK : ∀ z ∈ K, c * z = z * c := by
        intro z hz
        have hwK : b⁻¹ * z * b ∈ K := K.mul_mem (K.mul_mem (K.inv_mem hbK) hz) hbK
        have haz' : a * z = z * a := (hcomm z hz a haL).symm
        have ha_inv : a⁻¹ * z * a = z := by
          calc a⁻¹ * z * a = a⁻¹ * (a * z) := by rw [haz']; group
            _ = z := by group
        have hconj1 : (a * b)⁻¹ * z * (a * b) = b⁻¹ * z * b := by
          rw [mul_inv_rev]
          calc b⁻¹ * a⁻¹ * z * (a * b) = b⁻¹ * (a⁻¹ * z * a) * b := by group
            _ = b⁻¹ * z * b := by rw [ha_inv]
        have hxconj := hbinner _ hwK
        have hxconj' : x * (b⁻¹ * z * b) * x⁻¹ = z := by
          rw [hxconj]
          group
        have hcz : c * z * c⁻¹ = z := by
          calc c * z * c⁻¹ = x * ((a * b)⁻¹ * z * (a * b)) * x⁻¹ := by
                simp only [c]
                group
            _ = x * (b⁻¹ * z * b) * x⁻¹ := by rw [hconj1]
            _ = z := hxconj'
        calc c * z = (c * z * c⁻¹) * c := by group
          _ = z * c := by rw [hcz]
      have hcX : ∀ z ∈ L ⊔ K, c * z = z * c := by
        intro z hz
        rw [Subgroup.sup_eq_closure] at hz
        induction hz using Subgroup.closure_induction with
        | mem z hz =>
            rcases hz with hzL | hzK
            · exact hczL z hzL
            · exact hczK z hzK
        | one => simp
        | mul u v _ _ ihu ihv =>
            calc c * (u * v) = (c * u) * v := (mul_assoc _ _ _).symm
              _ = (u * c) * v := by rw [ihu]
              _ = u * (c * v) := mul_assoc _ _ _
              _ = u * (v * c) := by rw [ihv]
              _ = (u * v) * c := (mul_assoc _ _ _).symm
        | inv u _ ihu =>
            have h : c * u⁻¹ = u⁻¹ * c := by
              calc c * u⁻¹ = u⁻¹ * (u * c) * u⁻¹ := by group
                _ = u⁻¹ * (c * u) * u⁻¹ := by rw [ihu]
                _ = u⁻¹ * c := by group
            exact h
      have ha_pow : a ^ (5 ^ (k + 1)) = 1 := by
        rw [show 5 ^ (k + 1) = 5 * 5 ^ k by rw [pow_succ, Nat.mul_comm]]
        rw [pow_mul, ha5, one_pow]
      have hb_pow : b ^ (5 ^ (k + 1)) = 1 := by
        rw [show 5 ^ (k + 1) = 5 * 5 ^ k by rw [pow_succ, Nat.mul_comm]]
        rw [pow_mul, hb5, one_pow]
      have hcomm_ab : Commute a b := (hcomm b hbK a haL).symm
      have hab_pow : (a * b) ^ (5 ^ (k + 1)) = 1 := by
        rw [Commute.mul_pow hcomm_ab, ha_pow, hb_pow, one_mul]
      have hc_pow : c ^ (5 ^ (k + 1)) = 1 := by
        dsimp only [c]
        rw [Commute.mul_pow (show Commute x (a * b)⁻¹ from hxabinv), hxpow, inv_pow,
          hab_pow, inv_one, one_mul]
      have hc1 : c = 1 := eq_one_of_pow_five_pow_eq_one hcY hcX hno5 hc_pow
      have hxab : x = a * b := by
        have h : x * (a * b)⁻¹ = 1 := hc1
        calc x = x * (a * b)⁻¹ * (a * b) := by group
          _ = 1 * (a * b) := by rw [h]
          _ = a * b := one_mul _
      rw [hxab]
      exact (L ⊔ K).mul_mem (Subgroup.mem_sup_left haL) (Subgroup.mem_sup_right hbK)
  · refine sup_le (hM_le haL hcL.1) (hM_le haK hcK.1)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm13_10
