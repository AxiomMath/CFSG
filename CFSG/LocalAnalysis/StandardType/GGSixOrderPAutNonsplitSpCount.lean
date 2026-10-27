module

public import CFSG.LocalAnalysis.StandardType.GGSixBstarNoOffenderOmegaGenFrame

public section

namespace CFSG.StandardType

namespace OrdPNsGen

open Matrix Module SUTB NoOffOm

variable {K : Type} [Field K] [Finite K] [CharP K 2] {d : ℕ} {σ : K →+* K}
  {B : (Fin d → K) →ₛₗ[σ] (Fin d → K) →ₗ[K] K} {Γ : Subgroup (GL (Fin d) K)} {p : ℕ}
  {A : Subgroup (GL (Fin d) K)}

omit [Finite K] [CharP K 2] in
theorem pow_mem_of_inv {y : GL (Fin d) K} {W : Submodule K (Fin d → K)}
    (hWy : ∀ w ∈ W, glin y w ∈ W) (k : ℕ) : ∀ w ∈ W, glin (y ^ k) w ∈ W := by
  induction k with
  | zero => intro w hw; rw [pow_zero, glin_one]; exact hw
  | succ k ih =>
    intro w hw
    rw [pow_succ, glin_mul, Module.End.mul_apply]
    exact ih _ (hWy w hw)

omit [Finite K] in
theorem mod_eq_of_eqOn (hA : GenMax B Γ p A)
    {y : GL (Fin d) K} (hy : y ∈ A) {U : Submodule K (Fin d → K)} (hU : U ≤ grng y)
    (hUy : ∀ u ∈ U, glin y u ∈ U) (hU0 : U ≠ ⊥) {a b : ℕ}
    (hab : ∀ u ∈ U, glin (y ^ a) u = glin (y ^ b) u) : a % p = b % p := by
  have hp := hA.prime
  have hp1 : 1 ≤ p := hp.one_lt.le
  have hpb : b + (p - 1) * b = p * b := by
    obtain ⟨p', hp'⟩ : ∃ p', p = p' + 1 := ⟨p - 1, by omega⟩
    subst hp'
    simp only [Nat.add_sub_cancel]
    ring
  have hfix : ∀ u ∈ U, glin (y ^ (a + (p - 1) * b)) u = u := by
    intro u hu
    have hu' : glin (y ^ ((p - 1) * b)) u ∈ U := pow_mem_of_inv hUy _ u hu
    rw [pow_add, glin_mul, Module.End.mul_apply, hab _ hu', ← Module.End.mul_apply, ← glin_mul,
      ← pow_add, hpb, pow_mul, hA.pow y hy, one_pow, glin_one]
    rfl
  have hdvd : p ∣ a + (p - 1) * b := by
    by_contra hnd
    obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU0
    exact hu0 (eq_zero_of_pow_fix' hA hy hnd (hU hu) (hfix u hu))
  have h2 : a + (p - 1) * b + b = a + p * b := by
    rw [add_assoc, add_comm ((p - 1) * b) b, hpb]
  calc a % p = (a + p * b) % p := (Nat.add_mul_mod_self_left _ _ _).symm
    _ = (a + (p - 1) * b + b) % p := by rw [h2]
    _ = b % p := by rw [Nat.add_mod, Nat.mod_eq_zero_of_dvd hdvd, zero_add, Nat.mod_mod]

theorem finrank_genPieceSpan (hA : GenMax B Γ p A)
    {S : Finset (GL (Fin d) K)} (hS : GenPieceSet B A S) :
    finrank K (genPieceSpan S) = ∑ y ∈ S, finrank K (grng y) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [genPieceSpan]
  | insert y S hyS ih =>
    have hS' := hS.mono (Finset.subset_insert y S)
    have hX := (hS'.nondegOn_card hA).1
    have hsp : genPieceSpan (insert y S) = genPieceSpan S ⊔ grng y := by
      rw [genPieceSpan, Finset.iSup_insert, sup_comm]
    have horth := orth_genPieceSpan hA.symm hS hyS
    have hinf : genPieceSpan S ⊓ grng y = ⊥ := by
      refine (Submodule.eq_bot_iff _).mpr fun v hv => hX v hv.1 fun m hm => ?_
      exact (horth v hv.2 m hm).2
    have hfr := Submodule.finrank_sup_add_finrank_inf_eq (genPieceSpan S) (grng y)
    rw [hinf, finrank_bot, add_zero] at hfr
    rw [hsp, hfr, Finset.sum_insert hyS, ih hS', add_comm]

omit [Finite K] in
theorem GenPieceSet.minimal (hA : GenMax B Γ p A)
    {S : Finset (GL (Fin d) K)} (hS : GenPieceSet B A S) {y : GL (Fin d) K}
    (hy : y ∈ S) {W : Submodule K (Fin d → K)} (hWle : W ≤ grng y) (hW0 : W ≠ ⊥)
    (hWnd : NondegOn B W) (hWy : ∀ w ∈ W, glin y w ∈ W) : W = grng y := by
  have hyA : y ∈ A := hS.mem y hy
  have hp1 : 1 < p := hA.prime.one_lt
  have hWA : ∀ a ∈ A, ∀ w ∈ W, glin a w ∈ W := by
    intro a ha w hw
    obtain ⟨k, hk⟩ := hS.cyc y hy a ha
    rw [hk w (hWle hw)]
    exact pow_mem_of_inv hWy k w hw
  obtain ⟨b, hbA, hbW, hbW'⟩ := hA.exists_mem_restrict hWnd hWA hyA
  obtain ⟨k, hk⟩ := hS.cyc y hy b hbA
  have hk1 : k % p = 1 % p := by
    refine mod_eq_of_eqOn hA hyA hWle hWy hW0 fun w hw => ?_
    rw [← hk w (hWle hw), hbW w hw, pow_one]
  have hby : ∀ u ∈ grng y, glin b u = glin y u := by
    intro u hu
    rw [hk u hu, pow_eq_pow_mod k (hA.pow y hyA), hk1, Nat.mod_eq_of_lt hp1, pow_one]
  refine le_antisymm hWle fun v hv => ?_
  obtain ⟨m, hm, z, hz, rfl⟩ := exists_add_orth hWnd v
  have hzr : z ∈ grng y := by
    have : z = (m + z) - m := by abel
    rw [this]
    exact (grng y).sub_mem hv (hWle hm)
  have hz0 : z = 0 := eq_zero_of_mem_grng hA hyA hzr (by rw [← hby z hzr, hbW' z hz])
  rw [hz0, add_zero]
  exact hm

theorem card_eq_pow_of_terminal (hA : GenMax B Γ p A)
    {S : Finset (GL (Fin d) K)} (hS : GenPieceSet B A S)
    (hterm : ∀ c ∈ A, (∀ v ∈ genPieceSpan S, glin c v = v) → c = 1) :
    Nat.card A = p ^ S.card := by
  classical
  have : Fact p.Prime := ⟨hA.prime⟩
  have : NeZero p := ⟨hA.prime.ne_zero⟩
  have hp1 : 1 < p := hA.prime.one_lt
  have hyA : ∀ y : S, (y : GL (Fin d) K) ∈ A := fun y => hS.mem _ y.2
  have hrng : ∀ y : S, grng (y : GL (Fin d) K) ≠ ⊥ := fun y => grng_ne_bot (hS.ne_one _ y.2)
  have hinv : ∀ y : S, ∀ u ∈ grng (y : GL (Fin d) K),
      glin (y : GL (Fin d) K) u ∈ grng (y : GL (Fin d) K) :=
    fun y => grng_inv hA (hyA y) (hyA y)
  have hb : ∀ y : S, ∃ g ∈ A, (∀ w ∈ grng (y : GL (Fin d) K),
      glin g w = glin (y : GL (Fin d) K) w) ∧
        ∀ v ∈ (grng (y : GL (Fin d) K)).orthogonalBilin B, glin g v = v :=
    fun y => hA.exists_mem_restrict (nondegOn_grng hA (hyA y))
      (fun a ha => grng_inv hA (hyA y) ha) (hyA y)
  choose b hbA hbon hboff using hb
  have hbpow : ∀ (y : S) (k : ℕ), ∀ u ∈ grng (y : GL (Fin d) K),
      glin (b y ^ k) u = glin ((y : GL (Fin d) K) ^ k) u := by
    intro y k
    induction k with
    | zero => intro u _; rw [pow_zero, pow_zero]
    | succ k ih =>
      intro u hu
      have hyk : glin ((y : GL (Fin d) K) ^ k) u ∈ grng (y : GL (Fin d) K) :=
        pow_mem_of_inv (hinv y) k u hu
      rw [pow_succ', glin_mul, Module.End.mul_apply, ih u hu, hbon y _ hyk,
        ← Module.End.mul_apply, ← glin_mul, ← pow_succ']
  have hsub : ∀ y y' : S, y ≠ y' → ∀ u ∈ grng (y' : GL (Fin d) K),
      u ∈ (grng (y : GL (Fin d) K)).orthogonalBilin B := by
    intro y y' hyy' u hu
    refine Submodule.mem_orthogonalBilin.mpr fun m hm => ?_
    exact hS.orth _ y.2 _ y'.2 (fun e => hyy' (Subtype.ext e)) m hm u hu
  let : CommGroup A :=
    { (inferInstance : Group A) with
      mul_comm := fun a c => Subtype.ext (hA.comm _ a.2 _ c.2) }
  set bA : S → A := fun y => ⟨b y, hbA y⟩ with hbA'
  set Φ : (S → ZMod p) → A := fun s => ∏ y, bA y ^ (s y).val with hΦ
  have hact : ∀ (s : S → ZMod p) (y : S), ∀ u ∈ grng (y : GL (Fin d) K),
      glin ((Φ s : A) : GL (Fin d) K) u = glin ((y : GL (Fin d) K) ^ (s y).val) u := by
    intro s y u hu
    have hrest : (∏ y' ∈ Finset.univ.erase y, bA y' ^ (s y').val) ∈
        (genFixOn d K (grng (y : GL (Fin d) K) : Set (Fin d → K))).comap A.subtype := by
      refine Subgroup.prod_mem _ fun y' hy' => Subgroup.pow_mem _ ?_ _
      exact fun w hw => hboff y' w (hsub y' y (Finset.ne_of_mem_erase hy') w hw)
    have hrest' : glin ((∏ y' ∈ Finset.univ.erase y, bA y' ^ (s y').val : A) :
        GL (Fin d) K) u = u := hrest u hu
    simp only [hΦ]
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ y), Subgroup.coe_mul, glin_mul,
      Module.End.mul_apply, hrest', SubgroupClass.coe_pow, hbpow y _ u hu]
  have hinj : Function.Injective Φ := by
    intro s s' hss'
    funext y
    have h1 : (s y).val % p = (s' y).val % p := by
      refine mod_eq_of_eqOn hA (hyA y) le_rfl (hinv y) (hrng y) fun u hu => ?_
      rw [← hact s y u hu, ← hact s' y u hu, hss']
    rw [Nat.mod_eq_of_lt (ZMod.val_lt _), Nat.mod_eq_of_lt (ZMod.val_lt _)] at h1
    exact ZMod.val_injective p h1
  have hsurj : Function.Surjective Φ := by
    intro c
    have hk : ∀ y : S, ∃ k : ℕ, ∀ u ∈ grng (y : GL (Fin d) K),
        glin (c : GL (Fin d) K) u = glin ((y : GL (Fin d) K) ^ k) u :=
      fun y => hS.cyc _ y.2 _ c.2
    choose k hk using hk
    refine ⟨fun y => (k y : ZMod p), Subtype.ext ?_⟩
    set g : GL (Fin d) K := ((Φ fun y => (k y : ZMod p) : A) : GL (Fin d) K)
      with hg
    have hgA : g ∈ A := (Φ _).2
    have hag : ∀ y : S, ∀ u ∈ grng (y : GL (Fin d) K),
        glin g u = glin (c : GL (Fin d) K) u := by
      intro y u hu
      rw [hg, hact _ y u hu, hk y u hu, ZMod.val_natCast,
        ← pow_eq_pow_mod _ (hA.pow _ (hyA y))]
    have hle : genPieceSpan S ≤ LinearMap.ker (glin (g⁻¹ * (c : GL (Fin d) K)) - 1) := by
      refine iSup₂_le fun z hz => ?_
      intro u hu
      have h1 : glin g⁻¹ (glin g u) = u := by
        rw [← Module.End.mul_apply, ← glin_mul, inv_mul_cancel, glin_one]
        rfl
      rw [LinearMap.mem_ker, LinearMap.sub_apply, glin_mul, Module.End.mul_apply,
        ← hag ⟨z, hz⟩ u hu, h1, Module.End.one_apply, sub_self]
    have hc1 : g⁻¹ * (c : GL (Fin d) K) = 1 :=
      hterm _ (A.mul_mem (A.inv_mem hgA) c.2) fun v hv => sub_eq_zero.mp (hle hv)
    exact inv_mul_eq_one.mp hc1
  have hbij : Function.Bijective Φ := ⟨hinj, hsurj⟩
  rw [← Nat.card_congr (Equiv.ofBijective Φ hbij), Nat.card_fun, Nat.card_zmod,
    Nat.card_eq_finsetCard]

end OrdPNsGen

end CFSG.StandardType
