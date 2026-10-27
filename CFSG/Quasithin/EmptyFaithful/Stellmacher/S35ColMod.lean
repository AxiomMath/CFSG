module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35C1b4
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35C56Irr

public section

namespace CFSG.Quasithin.F53.Stellmacher.S35.Col

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.Quasithin.F53Mod
open CFSG.Quasithin.F53.Stellmacher.S35.C1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem exists_invariant_functional' {F V C Z : Subgroup G}
    (hq : Nonempty (OTwoQuot F ≃* Equiv.Perm (Fin 5))) (hCV : C ≤ V) (hZV : Z ≤ V)
    (hCL : ∀ c ∈ C, ∀ a ∈ oTwoRes F, ⁅a, c⁆ ∈ Z)
    (hQ : ∀ x ∈ V, ∀ q ∈ pCoreOf 2 F, ⁅x, q⁆ ∈ Z) (ho : IsOrthSec F C V) (l0 : G → ZMod 2)
    (h0 : ∀ x ∈ V, ∀ y ∈ V, l0 (x * y) = l0 x + l0 y) (h0Z : ∀ z ∈ Z, l0 z = 0) :
    ∃ l : G → ZMod 2, (∀ x ∈ V, ∀ y ∈ V, l (x * y) = l x + l y) ∧ (∀ c ∈ C, l c = l0 c) ∧
      ∀ a ∈ oTwoRes F, ∀ m ∈ V, l (a * m * a⁻¹) = l m := by
  classical
  have hcs : cSecIn F C V = pCoreOf 2 F := IsModelSec.cSecIn_eq_pCoreOf ho hq
  obtain ⟨θ, π, hθ, hθk, hmul, hker, hsurj, hequiv⟩ := exists_proj ho
  have hQθ : ∀ x : ↥F, θ x = 1 → (x : G) ∈ pCoreOf 2 F := fun x hx => by
    rw [← hcs]
    exact (mem_cSecIn_iff_of_ker hθk x.2).mp hx
  set L := oTwoRes F with hLdef
  have hLF : L ≤ F := oTwoRes_le F
  have hconj : ∀ k : ↥F, ∀ m ∈ V, (k : G)⁻¹ * m * k ∈ V ∧
      π ((k : G)⁻¹ * m * k) = orth.act (θ k)⁻¹ (π m) := by
    intro k m hm
    obtain ⟨h1, h2⟩ := hequiv k⁻¹ m hm
    rw [map_inv] at h2
    simpa using And.intro h1 h2
  have huniq : ∀ u u' : orth.W, (∀ m ∈ V, dotO u (π m) = dotO u' (π m)) → u = u' := by
    intro u u' h
    apply dotO_inj
    intro w
    obtain ⟨m, hm, rfl⟩ := hsurj w
    exact h m hm
  have hF : ∀ k : ↥F, (k : G) ∈ L → ∃ u : orth.W, ∀ m ∈ V, ddO l0 k m = dotO u (π m) := by
    intro k hkL
    have hkV : ∀ m ∈ V, (k : G)⁻¹ * m * k ∈ V := fun m hm => (hconj k m hm).1
    have hdc : ∀ c ∈ C, ddO l0 k c = 0 := by
      intro c hc
      have hz : (k : G)⁻¹ * c * k * c⁻¹ ∈ Z := by
        have := hCL c hc _ (L.inv_mem hkL)
        rwa [commutatorElement_def, inv_inv] at this
      have h1 : (k : G)⁻¹ * c * k = ((k : G)⁻¹ * c * k * c⁻¹) * c := by group
      unfold ddO
      rw [h1, h0 _ (hZV hz) c (hCV hc), h0Z _ hz, zero_add]
      exact CharTwo.add_self_eq_zero _
    have hwd : ∀ m ∈ V, ∀ m' ∈ V, π m = π m' → ddO l0 k m = ddO l0 k m' := by
      intro m hm m' hm' h
      have hcV : m⁻¹ * m' ∈ V := V.mul_mem (V.inv_mem hm) hm'
      have h1 : π m' = π m * π (m⁻¹ * m') := by
        rw [← hmul m hm _ hcV]
        congr 1
        group
      have hc1 : π (m⁻¹ * m') = 1 := by
        have : π m * π (m⁻¹ * m') = π m * 1 := by rw [mul_one, ← h1, h]
        exact mul_left_cancel this
      have hcC : m⁻¹ * m' ∈ C := (hker _ hcV).mp hc1
      have e : m' = m * (m⁻¹ * m') := by group
      rw [e, ddO_mul h0 hkV hm hcV, hdc _ hcC, add_zero]
    choose s hsV hsπ using hsurj
    have hφ : ∀ x y : orth.W, ddO l0 k (s (x * y)) = ddO l0 k (s x) + ddO l0 k (s y) := by
      intro x y
      rw [← ddO_mul h0 hkV (hsV x) (hsV y)]
      exact hwd _ (hsV _) _ (V.mul_mem (hsV x) (hsV y))
        (by rw [hsπ, hmul _ (hsV x) _ (hsV y), hsπ, hsπ])
    obtain ⟨u, hu⟩ := exists_dotO (fun w => ddO l0 k (s w)) hφ
    refine ⟨u, fun m hm => ?_⟩
    rw [← hu (π m)]
    exact hwd _ hm _ (hsV _) (hsπ _).symm
  choose! u hu using hF
  have hcoc : ∀ k k' : ↥F, (k : G) ∈ L → (k' : G) ∈ L →
      u (k * k') = u k * orth.act (θ k) (u k') := by
    intro k k' hk hk'
    have hkk : ((k * k' : ↥F) : G) ∈ L := L.mul_mem hk hk'
    apply huniq
    intro m hm
    calc dotO (u (k * k')) (π m) = ddO l0 ((k : G) * k') m := (hu (k * k') hkk m hm).symm
      _ = ddO l0 k' ((k : G)⁻¹ * m * k) + ddO l0 k m := ddO_cocycle l0 _ _ _
      _ = dotO (u k') (π ((k : G)⁻¹ * m * k)) + dotO (u k) (π m) := by
        rw [hu k' hk' _ (hconj k m hm).1, hu k hk m hm]
      _ = dotO (orth.act (θ k) (u k')) (π m) + dotO (u k) (π m) := by
        rw [(hconj k m hm).2, dotO_act_inv]
      _ = dotO (u k * orth.act (θ k) (u k')) (π m) := by
        rw [dotO_mul_left, add_comm]
  have hq1 : ∀ q : ↥F, (q : G) ∈ L → θ q = 1 → u q = 1 := by
    intro q hqL hθq
    apply huniq
    intro m hm
    rw [← hu q hqL m hm, dotO_one_left]
    exact ddO_eq_zero hZV h0 h0Z hQ (hQθ q hθq) hm
  have hJ : ∀ k k' : ↥F, (k : G) ∈ L → (k' : G) ∈ L → θ k = θ k' → u k = u k' := by
    intro k k' hk hk' hkk
    have hqL : (((k⁻¹ * k' : ↥F)) : G) ∈ L := L.mul_mem (L.inv_mem hk) hk'
    have hθq : θ (k⁻¹ * k') = 1 := by rw [map_mul, map_inv, hkk, inv_mul_cancel]
    have e : k' = k * (k⁻¹ * k') := by group
    rw [e, hcoc _ _ hk hqL, hq1 _ hqL hθq, map_one, mul_one]
  have hA : alternatingGroup (Fin 5) ≤ ((oTwoRes F).subgroupOf F).map θ :=
    S43.alt_le_map_oTwoRes hθ
  have hlift : ∀ σ : alternatingGroup (Fin 5), ∃ x : ↥F, (x : G) ∈ L ∧ θ x = σ.1 := fun σ => by
    obtain ⟨x, hx, hxθ⟩ := hA σ.2
    exact ⟨x, Subgroup.mem_subgroupOf.mp hx, hxθ⟩
  choose x hxL hxθ using hlift
  have hθA : ∀ k : ↥F, (k : G) ∈ L → θ k ∈ alternatingGroup (Fin 5) := fun k hk =>
    S43.map_oTwoRes_le_alt θ ⟨k, Subgroup.mem_subgroupOf.mpr hk, rfl⟩
  have hcocf : ∀ g h : alternatingGroup (Fin 5),
      u (x (g * h)) = u (x g) * orth.act (g : Equiv.Perm (Fin 5)) (u (x h)) := by
    intro g h
    have e1 : u (x (g * h)) = u (x g * x h) :=
      hJ _ _ (hxL _) (L.mul_mem (hxL g) (hxL h)) (by rw [map_mul, hxθ, hxθ, hxθ]; rfl)
    rw [e1, hcoc _ _ (hxL g) (hxL h), hxθ g]
  obtain ⟨w0, hw0⟩ := h1_alt5_orth (fun σ => u (x σ)) hcocf
  have huk : ∀ k : ↥F, (k : G) ∈ L → u k = orth.act (θ k) w0 * w0⁻¹ := by
    intro k hk
    have h1 : u k = u (x ⟨θ k, hθA k hk⟩) := hJ _ _ hk (hxL _) (hxθ ⟨θ k, hθA k hk⟩).symm
    rw [h1, hw0 ⟨θ k, hθA k hk⟩]
  have hw : w0⁻¹ = w0 := inv_eq_of_mul_eq_one_right (orth.sq w0)
  refine ⟨fun m => l0 m + dotO w0 (π m), ?_, ?_, ?_⟩
  · intro x hx y hy
    simp only
    rw [h0 x hx y hy, hmul x hx y hy, dotO_mul_right]
    ring
  · intro c hc
    have hπc : π c = 1 := (hker c (hCV hc)).mpr hc
    simp [hπc, dotO_one_right]
  · intro a ha m hm
    set k : ↥F := ⟨a⁻¹, F.inv_mem (hLF ha)⟩ with hkdef
    have hkL : (k : G) ∈ L := L.inv_mem ha
    have hA : a * m * a⁻¹ = (k : G)⁻¹ * m * k := by simp [hkdef]
    have hd := hu k hkL m hm
    have hp := (hconj k m hm).2
    have hu' := huk k hkL
    rw [hu', hw, dotO_mul_left] at hd
    unfold ddO at hd
    simp only
    rw [hA, hp, dotO_act_inv]
    have h2 : (2 : ZMod 2) = 0 := by decide
    linear_combination hd + (dotO (orth.act (θ k) w0) (π m) - l0 m) * h2


theorem inf_comm_le_of_orth {F V C Z : Subgroup G}
    (hq : Nonempty (OTwoQuot F ≃* Equiv.Perm (Fin 5)))
    (hFV : F ≤ Subgroup.normalizer (V : Set G))
    (hV2 : ∀ x ∈ V, x ^ 2 = 1) (hV : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x)
    (hZC : Z ≤ C) (hCV : C ≤ V) (hCL : ∀ c ∈ C, ∀ a ∈ oTwoRes F, ⁅a, c⁆ ∈ Z)
    (hQ : ⁅V, pCoreOf 2 F⁆ ≤ Z) (ho : IsOrthSec F C V) :
    C ⊓ ⁅V, oTwoRes F⁆ ≤ Z := by
  rintro c ⟨hcC, hcL⟩
  by_contra hcZ
  have hZV : Z ≤ V := hZC.trans hCV
  have hQ' : ∀ x ∈ V, ∀ q ∈ pCoreOf 2 F, ⁅x, q⁆ ∈ Z := fun x hx q hq' =>
    hQ (Subgroup.commutator_mem_commutator hx hq')
  obtain ⟨l0, h0, h0Z, h0c⟩ := exists_functional hV2 hV hZV (hCV hcC) hcZ
  obtain ⟨l, hadd, hlC, hinv⟩ :=
    exists_invariant_functional' hq hCV hZV hCL hQ' ho l0 h0 h0Z
  have hl1 : l 1 = 0 := by
    have h := hadd 1 V.one_mem 1 V.one_mem
    rw [mul_one] at h
    exact add_eq_left.mp h.symm
  let K : Subgroup G :=
    { carrier := {x | x ∈ V ∧ l x = 0}
      one_mem' := ⟨V.one_mem, hl1⟩
      mul_mem' := fun {x y} hx hy => ⟨V.mul_mem hx.1 hy.1, by rw [hadd x hx.1 y hy.1, hx.2, hy.2,
        add_zero]⟩
      inv_mem' := fun {x} hx => ⟨V.inv_mem hx.1, by
        have h := hadd x hx.1 x⁻¹ (V.inv_mem hx.1)
        rw [mul_inv_cancel, hl1, hx.2, zero_add] at h
        exact h.symm⟩ }
  have hle : ⁅V, oTwoRes F⁆ ≤ K := by
    rw [Subgroup.commutator_def, Subgroup.closure_le]
    rintro _ ⟨v, hv, a, ha, rfl⟩
    have hva : a * v⁻¹ * a⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.mp (hFV (oTwoRes_le F ha)) v⁻¹).mp (V.inv_mem hv)
    have e : ⁅v, a⁆ = v * (a * v⁻¹ * a⁻¹) := by rw [commutatorElement_def]; group
    refine ⟨by rw [e]; exact V.mul_mem hv hva, ?_⟩
    show l ⁅v, a⁆ = 0
    rw [e, hadd v hv _ hva, hinv a ha v⁻¹ (V.inv_mem hv)]
    have h := hadd v hv v⁻¹ (V.inv_mem hv)
    rw [mul_inv_cancel, hl1] at h
    exact h.symm
  have := (hle hcL).2
  rw [hlC c hcC, h0c] at this
  exact one_ne_zero this

omit [Finite G] in
theorem le_normalizer_comm {X A B : Subgroup G} (hA : X ≤ Subgroup.normalizer (A : Set G))
    (hB : X ≤ Subgroup.normalizer (B : Set G)) :
    X ≤ Subgroup.normalizer ((⁅A, B⁆ : Subgroup G) : Set G) := by
  intro h hh
  rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_commutator,
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hA hh),
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hB hh)]

theorem sup_comm_eq_of_orth {F V C : Subgroup G}
    (_hq : Nonempty (OTwoQuot F ≃* Equiv.Perm (Fin 5))) (hCV : C ≤ V)
    (ho : IsOrthSec F C V) : ⁅V, oTwoRes F⁆ ⊔ C = V := by
  have hsec := IsModelSec.isSec ho hCV
  have hFV := hsec.normN
  have hFC := hsec.normL
  have hLF : oTwoRes F ≤ F := oTwoRes_le F
  have hn : F ≤ Subgroup.normalizer ((⁅V, oTwoRes F⁆ ⊔ C : Subgroup G) : Set G) := by
    intro g hg
    have h1 := le_normalizer_comm (X := F) hFV (le_normalizer_oTwoRes F) hg
    rw [Subgroup.mem_normalizer_iff_map_conj_eq] at h1 ⊢
    rw [Subgroup.map_sup, h1, Subgroup.mem_normalizer_iff_map_conj_eq.mp (hFC hg)]
  have hVU : ⁅V, oTwoRes F⁆ ≤ V := by
    rw [Subgroup.commutator_le]
    intro x hx a ha
    have h1 := (Subgroup.mem_normalizer_iff.mp (hFV (hLF ha)) x⁻¹).mp (V.inv_mem hx)
    have : ⁅x, a⁆ = x * (a * x⁻¹ * a⁻¹) := by rw [commutatorElement_def]; group
    rw [this]
    exact V.mul_mem hx h1
  rcases IsOrthSec.eq_or_eq_of_oTwoRes ho (U := ⁅V, oTwoRes F⁆ ⊔ C) le_sup_right
      (sup_le hVU hCV) (fun a ha => hn (hLF ha)) with h | h
  · exfalso
    have hcomm : ⁅V, oTwoRes F⁆ ≤ C := h ▸ le_sup_left
    obtain ⟨θ, π, hθ, hθk, hmul, hker, hsurj, hequiv⟩ := exists_proj ho
    have hone : ∀ a : ↥F, (a : G) ∈ oTwoRes F → θ a = 1 := by
      intro a ha
      have : a ∈ θ.ker := by
        rw [hθk, Subgroup.mem_subgroupOf]
        refine Subgroup.subset_closure ⟨a.2, fun x hx => hcomm ?_⟩
        have h2 : (a : G) * x * (a : G)⁻¹ * x⁻¹ ∈ ⁅oTwoRes F, V⁆ :=
          Subgroup.commutator_mem_commutator ha hx
        rwa [Subgroup.commutator_comm] at h2
      exact this
    have hA : alternatingGroup (Fin 5) ≤ ((oTwoRes F).subgroupOf F).map θ :=
      S43.alt_le_map_oTwoRes hθ
    have hσ : (Equiv.swap (0 : Fin 5) 1 * Equiv.swap 1 2) ∈ alternatingGroup (Fin 5) := by
      rw [Equiv.Perm.mem_alternatingGroup]; decide
    obtain ⟨x, hx, hxσ⟩ := hA hσ
    have h1 := hone x (Subgroup.mem_subgroupOf.mp hx)
    rw [h1] at hxσ
    have : (Equiv.swap (0 : Fin 5) 1 * Equiv.swap 1 2) ≠ 1 := by decide
    exact this hxσ.symm
  · exact h

end CFSG.Quasithin.F53.Stellmacher.S35.Col
