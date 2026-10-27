module

public import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.Blocks
public import CFSG.Quasithin.Background.SimsD1TransGrp
public import CFSG.Foundations.QuasisimpleMulEquiv

public section

namespace CFSG.Quasithin.SimsD1.TransBlock

open CFSG.Open CFSG.QuasithinUnique

variable {A B : Type*} [Group A] [Group B]

theorem blockQ_map_eq (f : A →* B) (hf : Function.Injective f) (L : Subgroup A) :
    blockQ (L.map f) = (blockQ L).map f :=
  TransGrp.pCoreOf_map_eq f hf 2 L

theorem blockU_map_eq (f : A →* B) (hf : Function.Injective f) (L : Subgroup A) :
    blockU (L.map f) = (blockU L).map f := by
  unfold blockU
  rw [blockQ_map_eq f hf, Subgroup.map_commutator]

theorem blockZ_map_eq (f : A →* B) (hf : Function.Injective f) (L : Subgroup A) :
    blockZ (L.map f) = (blockZ L).map f := by
  unfold blockZ
  rw [blockU_map_eq f hf, TransGrp.map_inf_centralizer_eq f hf]

theorem noTwoQuotient_of_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    (h : ∀ (N : Subgroup X) [N.Normal], IsPGroup 2 (X ⧸ N) → N = ⊤) :
    ∀ (N : Subgroup Y) [N.Normal], IsPGroup 2 (Y ⧸ N) → N = ⊤ := by
  intro N _ hN
  have hmap : (N.comap e.toMonoidHom).map e.toMonoidHom = N :=
    Subgroup.map_comap_eq_self_of_surjective e.surjective N
  have htop := h (N.comap e.toMonoidHom) (hN.of_equiv (QuotientGroup.congr _ _ e hmap).symm)
  rw [← hmap, htop, Subgroup.map_top_of_surjective e.toMonoidHom e.surjective]

theorem forall_sq_eq_one_map_iff (f : A →* B) (hf : Function.Injective f) (K : Subgroup A) :
    (∀ x ∈ K.map f, x ^ 2 = 1) ↔ ∀ x ∈ K, x ^ 2 = 1 := by
  constructor
  · intro h x hx
    apply hf
    rw [map_pow, map_one]
    exact h (f x) ⟨x, hx, rfl⟩
  · rintro h _ ⟨x, hx, rfl⟩
    rw [← map_pow, h x hx, map_one]

theorem irreducible_map_iff (f : A →* B) (hf : Function.Injective f) (L Z U : Subgroup A) :
    (∀ W : Subgroup B, Z.map f ≤ W → W ≤ U.map f →
      L.map f ≤ Subgroup.normalizer (W : Set B) → W = Z.map f ∨ W = U.map f) ↔
    ∀ W : Subgroup A, Z ≤ W → W ≤ U → L ≤ Subgroup.normalizer (W : Set A) → W = Z ∨ W = U := by
  constructor
  · intro h W hZW hWU hLW
    exact (h (W.map f) (Subgroup.map_mono hZW) (Subgroup.map_mono hWU)
      ((TransGrp.le_normalizer_map_iff f hf L W).2 hLW)).imp
      (fun h1 => Subgroup.map_injective hf h1) (fun h1 => Subgroup.map_injective hf h1)
  · intro h W' hZW hWU hLW
    obtain ⟨W, rfl⟩ := TransGrp.exists_map_eq_of_le_map f hWU
    rw [Subgroup.map_le_map_iff_of_injective hf] at hZW hWU
    exact (h W hZW hWU ((TransGrp.le_normalizer_map_iff f hf L W).1 hLW)).imp
      (congrArg (Subgroup.map f)) (congrArg (Subgroup.map f))

theorem isShort2_map_iff (f : A →* B) (hf : Function.Injective f) (L : Subgroup A) :
    IsShort2 (L.map f) ↔ IsShort2 L := by
  let e : ↥L ≃* ↥(L.map f) := L.equivMapOfInjective f hf
  let q : (↥L ⧸ CFSG.pCore 2 ↥L) ≃* (↥(L.map f) ⧸ CFSG.pCore 2 ↥(L.map f)) :=
    QuotientGroup.congr _ _ e (CFSG.pCore_map_iso 2 e)
  unfold IsShort2
  rw [blockU_map_eq f hf, blockQ_map_eq f hf, blockZ_map_eq f hf,
    ← TransGrp.map_inf_centralizer_eq f hf]
  refine and_congr ⟨noTwoQuotient_of_mulEquiv e.symm, noTwoQuotient_of_mulEquiv e⟩
    (and_congr (TransGrp.charTwo_map_iff f hf L)
      (and_congr (and_congr (Subgroup.map_le_map_iff_of_injective hf)
        (forall_sq_eq_one_map_iff f hf _))
      (and_congr (or_congr (CFSG.IsQuasisimple.congr q).symm ?_)
        (and_congr (Subgroup.map_lt_map_iff_of_injective hf) (irreducible_map_iff f hf L _ _)))))
  rw [← Nat.card_congr q.toEquiv]

theorem isSubnormal_subgroupOf_map_iff (f : A →* B) (hf : Function.Injective f)
    (X L : Subgroup A) :
    ((L.map f).subgroupOf (X.map f)).IsSubnormal ↔ (L.subgroupOf X).IsSubnormal := by
  let e : ↥X ≃* ↥(X.map f) := X.equivMapOfInjective f hf
  have h : ((L.map f).subgroupOf (X.map f)).comap e.toMonoidHom = L.subgroupOf X := by
    ext x
    show f x ∈ L.map f ↔ (x : A) ∈ L
    exact Subgroup.mem_map_iff_mem hf
  refine ⟨fun h' => h ▸ h'.comap e.toMonoidHom, fun h' => ?_⟩
  have h'' := h'.map (f := e.toMonoidHom) e.surjective
  rwa [← h, Subgroup.map_comap_eq_self_of_surjective e.surjective] at h''

theorem isBlock2_map_iff (f : A →* B) (hf : Function.Injective f) (X L : Subgroup A) :
    IsBlock2 (X.map f) (L.map f) ↔ IsBlock2 X L :=
  and_congr (isShort2_map_iff f hf L) (and_congr (Subgroup.map_le_map_iff_of_injective hf)
    (isSubnormal_subgroupOf_map_iff f hf X L))

theorem isAltType_of_mulEquiv {G H : Type*} [Group G] [Group H] {L : Subgroup G}
    {L' : Subgroup H} (φ : ↥L ≃* ↥L') (ψ : ↥(blockU L) ≃* ↥(blockU L'))
    (hZ : ∀ u : ↥(blockU L), ((ψ u : ↥(blockU L')) : H) ∈ blockZ L' ↔ (u : G) ∈ blockZ L)
    (hc : ∀ (ℓ : ↥L) (u v : ↥(blockU L)), (v : G) = ℓ * u * ℓ⁻¹ →
      ((ψ v : ↥(blockU L')) : H) = φ ℓ * ψ u * (φ ℓ)⁻¹)
    {m : ℕ} (h : IsAltType L' m) : IsAltType L m := by
  obtain ⟨α, hαs, hαk, β, hβs, hβk, hβe⟩ := h
  refine ⟨α.comp φ.toMonoidHom, hαs.comp φ.surjective, ?_, β.comp ψ.toMonoidHom,
    hβs.comp ψ.surjective, ?_, fun ℓ u v huv i => hβe (φ ℓ) (ψ u) (ψ v) (hc ℓ u v huv) i⟩
  · rw [← MonoidHom.comap_ker, hαk, ← CFSG.pCore_map_iso 2 φ,
      Subgroup.comap_map_eq_self_of_injective φ.injective]
  · ext u
    rw [← MonoidHom.comap_ker, hβk, Subgroup.mem_comap, Subgroup.mem_subgroupOf,
      Subgroup.mem_subgroupOf]
    exact hZ u

theorem isAltType_map_iff (f : A →* B) (hf : Function.Injective f) (L : Subgroup A) (m : ℕ) :
    IsAltType (L.map f) m ↔ IsAltType L m := by
  let e : ↥L ≃* ↥(L.map f) := L.equivMapOfInjective f hf
  let ψ : ↥(blockU L) ≃* ↥(blockU (L.map f)) :=
    ((blockU L).equivMapOfInjective f hf).trans
      (MulEquiv.subgroupCongr (blockU_map_eq f hf L).symm)
  have he : ∀ x : ↥L, ((e x : ↥(L.map f)) : B) = f x := fun _ => rfl
  have hψ : ∀ u : ↥(blockU L), ((ψ u : ↥(blockU (L.map f))) : B) = f u := fun _ => rfl
  have hZ : ∀ u : ↥(blockU L),
      ((ψ u : ↥(blockU (L.map f))) : B) ∈ blockZ (L.map f) ↔ (u : A) ∈ blockZ L := fun u => by
    rw [hψ, blockZ_map_eq f hf, Subgroup.mem_map_iff_mem hf]
  constructor
  · refine isAltType_of_mulEquiv e ψ hZ fun ℓ u v h => ?_
    simp only [hψ, he, h, map_mul, InvMemClass.coe_inv, map_inv]
  · have hψs : ∀ w, f ((ψ.symm w : ↥(blockU L)) : A) = (w : B) := fun w => by
      rw [← hψ, MulEquiv.apply_symm_apply]
    have hes : ∀ w, f ((e.symm w : ↥L) : A) = (w : B) := fun w => by
      rw [← he, MulEquiv.apply_symm_apply]
    refine isAltType_of_mulEquiv e.symm ψ.symm (fun w => ?_) fun ℓ u v h => hf ?_
    · rw [← hZ (ψ.symm w), MulEquiv.apply_symm_apply]
    · simp only [map_mul, InvMemClass.coe_inv, map_inv, hψs, hes, h]

theorem prodA3_map_iff (f : A →* B) (hf : Function.Injective f) (X Y : Subgroup A) :
    (∃ S : Finset (Subgroup B), (∀ L ∈ S, IsBlock2 (X.map f) L ∧ IsAltType L 3) ∧
      Y.map f = ⨆ L ∈ S, L) ↔
    (∃ S : Finset (Subgroup A), (∀ L ∈ S, IsBlock2 X L ∧ IsAltType L 3) ∧ Y = ⨆ L ∈ S, L) := by
  classical
  constructor
  · rintro ⟨S, hS, hY⟩
    have hmc : ∀ L ∈ S, (L.comap f).map f = L := fun L hL =>
      TransGrp.map_comap_of_le_map f (hS L hL).1.2.1
    refine ⟨S.image (Subgroup.comap f), fun K hK => ?_, Subgroup.map_injective hf ?_⟩
    · obtain ⟨L, hL, rfl⟩ := Finset.mem_image.1 hK
      have h := hS L hL
      rw [← hmc L hL] at h
      exact ⟨(isBlock2_map_iff f hf X _).1 h.1, (isAltType_map_iff f hf _ 3).1 h.2⟩
    · simp only [Subgroup.map_iSup, Finset.iSup_finset_image]
      rw [hY]
      exact biSup_congr fun L hL => (hmc L hL).symm
  · rintro ⟨S, hS, rfl⟩
    refine ⟨S.image (Subgroup.map f), fun K hK => ?_, ?_⟩
    · obtain ⟨L, hL, rfl⟩ := Finset.mem_image.1 hK
      exact ⟨(isBlock2_map_iff f hf X L).2 (hS L hL).1, (isAltType_map_iff f hf L 3).2 (hS L hL).2⟩
    · simp only [Subgroup.map_iSup, Finset.iSup_finset_image]

end CFSG.Quasithin.SimsD1.TransBlock
