module

public import CFSG.Quasithin.EmptyFaithful.S143KI

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique

namespace S143

open A6Model

theorem mat_ext {M N : Mat4} (h : ∀ w, vm w M = vm w N) : M = N := by
  have h0 := h ⟨true, false, false, false⟩
  have h1 := h ⟨false, true, false, false⟩
  have h2 := h ⟨false, false, true, false⟩
  have h3 := h ⟨false, false, false, true⟩
  rw [vm_e0, vm_e0] at h0
  rw [vm_e1, vm_e1] at h1
  rw [vm_e2, vm_e2] at h2
  rw [vm_e3, vm_e3] at h3
  obtain ⟨a0, a1, a2, a3⟩ := M
  obtain ⟨b0, b1, b2, b3⟩ := N
  simp only at h0 h1 h2 h3
  rw [h0, h1, h2, h3]

theorem mat_eq_I4 {M : Mat4} (h : ∀ w, vm w M = w) : M = I4 :=
  mat_ext fun w => by rw [h w, vm_I4]

section Hom

variable {G : Type*} [Group G] {A : Subgroup G} {e0 e1 e2 e3 : G} (hB : IsBasis A e0 e1 e2 e3)
  {cm : Mat4} (hcm : ∀ v w : V4, vm v cm = vm w cm → v = w)

include hcm

theorem psi_surjective : Function.Surjective (psi cm) := by
  have hinj : Function.Injective (psi cm) := fun v w h => psi_inj hcm h
  have hb : Function.Bijective (psi cm) :=
    hinj.bijective_of_nat_card_le (by rw [V4.card, n6_card])
  exact hb.2

theorem perm_eq_of_act {σ σ' : Equiv.Perm (Fin 6)} (hs : σ.sign = 1) (hs' : σ'.sign = 1)
    (h : ∀ w, n6Act σ (psi cm w) = n6Act σ' (psi cm w)) : σ = σ' := by
  have hact : n6Act σ = n6Act σ' := by
    refine MulEquiv.ext fun a => ?_
    obtain ⟨w, rfl⟩ := psi_surjective hcm a
    exact h w
  have h1 : n6Act (σ'⁻¹ * σ) = 1 := by
    rw [map_mul, map_inv, hact]; exact inv_mul_cancel _
  have := n6_faithful (σ'⁻¹ * σ)
    (Equiv.Perm.mem_alternatingGroup.mpr (by rw [Equiv.Perm.sign_mul, Equiv.Perm.sign_inv, hs, hs']; rfl)) h1
  exact (inv_mul_eq_one.mp this).symm

omit hcm

variable {K : Subgroup G} (hK : K ≤ GoodSub hB cm)

noncomputable def sigmaOfK (k : ↥K) : Equiv.Perm (Fin 6) := Classical.choose (hK k.2).2

theorem sigmaOfK_spec (k : ↥K) :
    (sigmaOfK hB hK k).sign = 1 ∧ ∀ w : V4, n6Act (sigmaOfK hB hK k) (psi cm w) =
      psi cm (vm w (cmat e0 e1 e2 e3 (k : G))) :=
  Classical.choose_spec (hK k.2).2

include hcm

noncomputable def homK : ↥K →* ↥(alternatingGroup (Fin 6)) :=
  MonoidHom.mk' (fun k => ⟨sigmaOfK hB hK k, Equiv.Perm.mem_alternatingGroup.mpr (sigmaOfK_spec hB hK k).1⟩)
    (fun k₁ k₂ => by
      apply Subtype.ext
      show sigmaOfK hB hK (k₁ * k₂) = sigmaOfK hB hK k₁ * sigmaOfK hB hK k₂
      refine perm_eq_of_act hcm (sigmaOfK_spec hB hK _).1 ?_ ?_
      · rw [Equiv.Perm.sign_mul, (sigmaOfK_spec hB hK k₁).1, (sigmaOfK_spec hB hK k₂).1]; rfl
      · intro w
        have hk₁ := (hK k₁.2).1
        have hk₂ := (hK k₂.2).1
        calc n6Act (sigmaOfK hB hK (k₁ * k₂)) (psi cm w)
            = psi cm (vm w (cmat e0 e1 e2 e3 ((k₁ * k₂ : ↥K) : G))) :=
              (sigmaOfK_spec hB hK (k₁ * k₂)).2 w
          _ = psi cm (vm (vm w (cmat e0 e1 e2 e3 (k₂ : G))) (cmat e0 e1 e2 e3 (k₁ : G))) := by
              rw [vm_vm]
              show psi cm (vm w (cmat e0 e1 e2 e3 ((k₁ : G) * (k₂ : G)))) = _
              rw [hB.cmat_mul hk₁ hk₂]
          _ = n6Act (sigmaOfK hB hK k₁) (psi cm (vm w (cmat e0 e1 e2 e3 (k₂ : G)))) :=
              ((sigmaOfK_spec hB hK k₁).2 _).symm
          _ = n6Act (sigmaOfK hB hK k₁) (n6Act (sigmaOfK hB hK k₂) (psi cm w)) := by
              rw [(sigmaOfK_spec hB hK k₂).2 w]
          _ = n6Act (sigmaOfK hB hK k₁ * sigmaOfK hB hK k₂) (psi cm w) := by
              rw [map_mul]; rfl)

theorem homK_apply (k : ↥K) :
    ((homK hB hcm hK k : ↥(alternatingGroup (Fin 6))) : Equiv.Perm (Fin 6)) = sigmaOfK hB hK k := by
  unfold homK
  rfl

theorem homK_eq_one_iff (k : ↥K) : homK hB hcm hK k = 1 ↔ cmat e0 e1 e2 e3 (k : G) = I4 := by
  constructor
  · intro h
    have hσ : sigmaOfK hB hK k = 1 := congrArg Subtype.val h
    have h2 := (sigmaOfK_spec hB hK k).2
    refine mat_eq_I4 fun w => psi_inj hcm ?_
    rw [← h2 w, hσ]
    simp
  · intro h
    apply Subtype.ext
    show sigmaOfK hB hK k = 1
    refine perm_eq_of_act hcm (sigmaOfK_spec hB hK k).1 (by simp) fun w => ?_
    rw [(sigmaOfK_spec hB hK k).2 w, h, vm_I4]
    simp

theorem cmat_eq_of_homK_eq {k₁ k₂ : ↥K} (h : homK hB hcm hK k₁ = homK hB hcm hK k₂) :
    cmat e0 e1 e2 e3 (k₁ : G) = cmat e0 e1 e2 e3 (k₂ : G) := by
  have hσ : sigmaOfK hB hK k₁ = sigmaOfK hB hK k₂ := congrArg Subtype.val h
  refine mat_ext fun w => psi_inj hcm ?_
  rw [← (sigmaOfK_spec hB hK k₁).2 w, ← (sigmaOfK_spec hB hK k₂).2 w, hσ]

theorem homK_surjective {x y : G} (hxK : x ∈ K) (hyK : y ∈ K)
    (hcount : (closureCodes [cmat e0 e1 e2 e3 x, cmat e0 e1 e2 e3 y]).length = 360) :
    Function.Surjective (homK hB hcm hK) := by
  classical
  obtain ⟨hLc, hnd⟩ := closureCodes_spec [cmat e0 e1 e2 e3 x, cmat e0 e1 e2 e3 y]
  have hN : ∀ k ∈ K, k ∈ Subgroup.normalizer (A : Set G) := fun k hk => (hK hk).1
  have hgen : ∀ M, InGen [cmat e0 e1 e2 e3 x, cmat e0 e1 e2 e3 y] M →
      ∃ k ∈ K, cmat e0 e1 e2 e3 k = M := by
    intro M hM
    induction hM with
    | one => exact ⟨1, K.one_mem, hB.cmat_one⟩
    | mul hM' hg ih =>
      obtain ⟨k, hkK, rfl⟩ := ih
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl
      · exact ⟨x * k, K.mul_mem hxK hkK, hB.cmat_mul (hN x hxK) (hN k hkK)⟩
      · exact ⟨y * k, K.mul_mem hyK hkK, hB.cmat_mul (hN y hyK) (hN k hkK)⟩
  have hex : ∀ cd ∈ closureCodes [cmat e0 e1 e2 e3 x, cmat e0 e1 e2 e3 y],
      ∃ k ∈ K, pack (cmat e0 e1 e2 e3 k) = cd := by
    intro cd hcd
    obtain ⟨M, hM, rfl⟩ := hLc cd hcd
    obtain ⟨k, hkK, rfl⟩ := hgen M hM
    exact ⟨k, hkK, rfl⟩
  let s : Finset ℕ := (closureCodes [cmat e0 e1 e2 e3 x, cmat e0 e1 e2 e3 y]).toFinset
  let kc : ∀ cd ∈ s, ↥K := fun cd hcd =>
    ⟨Classical.choose (hex cd (List.mem_toFinset.mp hcd)),
      (Classical.choose_spec (hex cd (List.mem_toFinset.mp hcd))).1⟩
  have hkc : ∀ cd (hcd : cd ∈ s), pack (cmat e0 e1 e2 e3 (kc cd hcd : G)) = cd := fun cd hcd =>
    (Classical.choose_spec (hex cd (List.mem_toFinset.mp hcd))).2
  have hs : s.card = 360 := by
    rw [List.toFinset_card_of_nodup hnd]; exact hcount
  have hinj : ∀ a₁ a₂ (ha₁ : a₁ ∈ s) (ha₂ : a₂ ∈ s),
      homK hB hcm hK (kc a₁ ha₁) = homK hB hcm hK (kc a₂ ha₂) → a₁ = a₂ := by
    intro a₁ a₂ ha₁ ha₂ h
    rw [← hkc a₁ ha₁, ← hkc a₂ ha₂, cmat_eq_of_homK_eq hB hcm hK h]
  have hcardA : (Finset.univ : Finset ↥(alternatingGroup (Fin 6))).card = 360 := by
    rw [Finset.card_univ, card_alternatingGroup]
    simp [Fintype.card_fin, Nat.factorial]
  intro σ
  obtain ⟨cd, hcd, hσ⟩ := Finset.surj_on_of_inj_on_of_card_le
    (s := s) (t := (Finset.univ : Finset ↥(alternatingGroup (Fin 6))))
    (fun cd hcd => homK hB hcm hK (kc cd hcd)) (fun _ _ => Finset.mem_univ _) hinj
    (by rw [hs, hcardA]) σ (Finset.mem_univ σ)
  exact ⟨kc cd hcd, hσ.symm⟩

end Hom

end S143

end CFSG.Quasithin
