module

public import CFSG.Quasithin.Background.B1MoreSevenB

public section

namespace CFSG.Quasithin

open CFSG.Open

variable {V : Type*} [CommGroup V]

namespace B72Hyp

variable {H A : Subgroup (MulAut V)} {a : MulAut V} {I : Subgroup V}

theorem I_le_Xplus (P : B72Hyp H A a I) :
    I ≤ (Dsub a I ⊔ commSub (Dsub a I) H) ⊔ fixV H := by
  obtain ⟨invI, -, -, -⟩ := mem_irrPlus_top_iff.1 P.hI
  obtain ⟨invI', -, -, irrI'⟩ := mem_irrPlus_top_iff.1 P.irr'
  set Z := fixV H with hZ
  set D := Dsub a I with hD
  set I' := I.map a.toMonoidHom with hI'
  set Xp := (D ⊔ commSub D H) ⊔ Z with hXp
  have hXinv : ∀ h ∈ H, ∀ y ∈ Xp, h y ∈ Xp :=
    isInv_sup (sup_commSub_inv H D) (isInv_fixV H)
  have hKinv : ∀ h ∈ H, ∀ w ∈ Xp ⊓ I', h w ∈ Xp ⊓ I' := isInv_inf hXinv invI'
  have hKge : I' ⊓ Z ≤ Xp ⊓ I' := fun w hw => ⟨Subgroup.mem_sup_right hw.2, hw.1⟩
  have hDX : D ≤ Xp := le_sup_left.trans le_sup_left
  rcases irrI' (Xp ⊓ I') hKinv hKge inf_le_right with h | h
  · exfalso
    apply P.not_invariant_DZ
    intro h' hh x hx
    obtain ⟨d, hd, z, hz, rfl⟩ := Subgroup.mem_sup.1 hx
    obtain ⟨j, hj, rfl⟩ := mem_Dsub.1 hd
    have hhj : h' j ∈ I := invI h' hh j hj
    have hd'D : a (h' j) * (h' j)⁻¹ ∈ D := mem_Dsub.2 ⟨h' j, hhj, rfl⟩
    have haj : a j ∈ I' := ⟨j, hj, rfl⟩
    have hahj : a (h' j) ∈ I' := ⟨h' j, hhj, rfl⟩
    have hrI' : h' (a j) * (a (h' j))⁻¹ ∈ I' :=
      I'.mul_mem (invI' h' hh _ haj) (I'.inv_mem hahj)
    have hrX : h' (a j) * (a (h' j))⁻¹ ∈ Xp := by
      have e : h' (a j) * (a (h' j))⁻¹ = h' (a j * j⁻¹) * (a (h' j) * (h' j)⁻¹)⁻¹ := by
        rw [map_mul, map_inv]; cgroup
      rw [e]
      exact Xp.mul_mem (hXinv h' hh _ (hDX hd)) (Xp.inv_mem (hDX hd'D))
    have hrZ : h' (a j) * (a (h' j))⁻¹ ∈ Z := by
      have : h' (a j) * (a (h' j))⁻¹ ∈ Xp ⊓ I' := ⟨hrX, hrI'⟩
      rw [h] at this
      exact this.2
    have e : h' (a j * j⁻¹ * z) =
        (h' (a j) * (a (h' j))⁻¹) * (a (h' j) * (h' j)⁻¹) * z := by
      rw [map_mul, map_mul, map_inv, hz h' hh]; cgroup
    rw [e]
    exact (D ⊔ Z).mul_mem ((D ⊔ Z).mul_mem (Subgroup.mem_sup_right hrZ) (Subgroup.mem_sup_left hd'D))
      (Subgroup.mem_sup_right hz)
  · have hI'le : I' ≤ Xp := fun w hw => by
      have : w ∈ Xp ⊓ I' := by rw [h]; exact hw
      exact this.1
    intro i hi
    have h1 : a i ∈ Xp := hI'le ⟨i, hi, rfl⟩
    have h2 : a i * i⁻¹ ∈ Xp := hDX (mem_Dsub.2 ⟨i, hi, rfl⟩)
    have := Xp.mul_mem (Xp.inv_mem h2) h1
    simpa using this

theorem W_eq (P : B72Hyp H A a I) :
    I ⊔ I.map a.toMonoidHom = commSub (Dsub a I) H := by
  obtain ⟨invI, commI, -, -⟩ := mem_irrPlus_top_iff.1 P.hI
  obtain ⟨invI', commI', -, -⟩ := mem_irrPlus_top_iff.1 P.irr'
  have hDX : Dsub a I ≤ (Dsub a I ⊔ commSub (Dsub a I) H) ⊔ fixV H :=
    le_sup_left.trans le_sup_left
  have hI'le : I.map a.toMonoidHom ≤ (Dsub a I ⊔ commSub (Dsub a I) H) ⊔ fixV H := by
    rintro _ ⟨i, hi, rfl⟩
    have h1 := P.I_le_Xplus hi
    have h2 := hDX (mem_Dsub.2 ⟨i, hi, rfl⟩)
    have := Subgroup.mul_mem _ h2 h1
    simpa using this
  have hW : I ⊔ I.map a.toMonoidHom ≤ (Dsub a I ⊔ commSub (Dsub a I) H) ⊔ fixV H :=
    sup_le P.I_le_Xplus hI'le
  have hIc : I ≤ commSub (I ⊔ I.map a.toMonoidHom) H := by
    calc I = commSub I H := commI.symm
      _ ≤ _ := commSub_mono le_sup_left le_rfl
  have hI'c : I.map a.toMonoidHom ≤ commSub (I ⊔ I.map a.toMonoidHom) H := by
    calc I.map a.toMonoidHom = commSub (I.map a.toMonoidHom) H := commI'.symm
      _ ≤ _ := commSub_mono le_sup_right le_rfl
  have hWc : I ⊔ I.map a.toMonoidHom ≤ commSub (I ⊔ I.map a.toMonoidHom) H := sup_le hIc hI'c
  have hstep : commSub ((Dsub a I ⊔ commSub (Dsub a I) H) ⊔ fixV H) H =
      commSub (Dsub a I ⊔ commSub (Dsub a I) H) H := commSub_sup_fixV le_rfl
  refine le_antisymm ?_ ?_
  · calc I ⊔ I.map a.toMonoidHom ≤ commSub (I ⊔ I.map a.toMonoidHom) H := hWc
      _ ≤ commSub ((Dsub a I ⊔ commSub (Dsub a I) H) ⊔ fixV H) H := commSub_mono hW le_rfl
      _ = commSub (Dsub a I ⊔ commSub (Dsub a I) H) H := hstep
      _ ≤ commSub (Dsub a I) H := commSub_sup_le_self H (Dsub a I)
  · calc commSub (Dsub a I) H ≤ commSub (I ⊔ I.map a.toMonoidHom) H :=
          commSub_mono (Dsub_le_W a I) le_rfl
      _ ≤ I ⊔ I.map a.toMonoidHom := commSub_le_of_invariant (isInv_sup invI invI')

theorem W_inv_A (P : B72Hyp H A a I) :
    ∀ b ∈ A, ∀ w ∈ I ⊔ I.map a.toMonoidHom, b w ∈ I ⊔ I.map a.toMonoidHom := by
  intro b hb y hy
  rw [P.W_eq] at hy ⊢
  refine Subgroup.closure_induction (p := fun y _ => b y ∈ commSub (Dsub a I) H) ?_ ?_ ?_ ?_ hy
  · rintro _ ⟨g, hg, x, hx, rfl⟩
    have hbx : b x = x := P.Dsub_fixed hb hx
    have hbx' : b⁻¹ x = x := P.Dsub_fixed (A.inv_mem hb) hx
    have e : b (g x * x⁻¹) = (b * g * b⁻¹) x * x⁻¹ := by
      rw [map_mul, map_inv, hbx]
      simp [MulAut.mul_apply, hbx']
    rw [e]
    exact Subgroup.subset_closure ⟨b * g * b⁻¹, P.conj_mem hb hg, x, hx, rfl⟩
  · simp
  · intro x y _ _ hx hy
    simpa using Subgroup.mul_mem _ hx hy
  · intro x _ hx
    simpa using Subgroup.inv_mem _ hx

theorem stab_trivial_mod (P : B72Hyp H A a I) {b : MulAut V} (hb : b ∈ A)
    (hbI : ∀ x, b x ∈ I ↔ x ∈ I) :
    ∀ w ∈ I ⊔ I.map a.toMonoidHom, b w * w⁻¹ ∈ fixV H := by
  set Z := fixV H with hZ
  set I' := I.map a.toMonoidHom with hI'
  have hab : ∀ x, b (a x) = a (b x) := fun x => by
    have := P.abel b hb a P.ha
    simpa [MulAut.mul_apply] using congrArg (fun φ : MulAut V => φ x) this
  have step1 : ∀ x ∈ I, b x * x⁻¹ ∈ Z := by
    intro x hx
    have huI : b x * x⁻¹ ∈ I := I.mul_mem ((hbI x).2 hx) (I.inv_mem hx)
    have hau : a (b x * x⁻¹) = b x * x⁻¹ := by
      have h1 := P.hcomm b hb x
      rw [map_mul, map_inv, hab] at h1
      have h2 : a (b x) = a x * x⁻¹ * b x := by
        calc a (b x) = (a (b x) * (b x)⁻¹) * b x := by group
          _ = _ := by rw [h1]
      rw [map_mul, map_inv, h2]; cgroup
    have huI' : b x * x⁻¹ ∈ I' := ⟨_, huI, hau⟩
    have : b x * x⁻¹ ∈ (I ⊔ Z) ⊓ (I' ⊔ Z) :=
      ⟨Subgroup.mem_sup_left huI, Subgroup.mem_sup_left huI'⟩
    rwa [P.disj] at this
  intro w hw
  obtain ⟨i, hi, j, hj, rfl⟩ := Subgroup.mem_sup.1 hw
  obtain ⟨x, hx, hxj⟩ := hj
  have hxj' : a x = j := hxj
  subst hxj'
  have e : b (i * a x) * (i * a x)⁻¹ = (b i * i⁻¹) * a (b x * x⁻¹) := by
    simp only [map_mul, map_inv, hab]; cgroup
  rw [e]
  exact Z.mul_mem (step1 i hi) (P.fixV_inv P.ha (step1 x hx))

theorem fixes_of_trivial_mod [Finite V] (hV : ∀ v : V, v ^ 2 = 1) (P : B72Hyp H A a I)
    (hH : oTwoUpper H = H) (hCF : AllTwoChiefFactorsCentral H) {b : MulAut V} (hb : b ∈ A)
    (hbZ : ∀ w ∈ I ⊔ I.map a.toMonoidHom, b w * w⁻¹ ∈ fixV H) :
    b ∈ centSub (I ⊔ I.map a.toMonoidHom) := by
  obtain ⟨invI, commI, -, -⟩ := mem_irrPlus_top_iff.1 P.hI
  obtain ⟨invI', commI', -, -⟩ := mem_irrPlus_top_iff.1 P.irr'
  set W := I ⊔ I.map a.toMonoidHom with hW
  set Z := fixV H with hZ
  have hWH : ∀ h ∈ H, ∀ w ∈ W, h w ∈ W := isInv_sup invI invI'
  have hWA : ∀ c ∈ A, ∀ w ∈ W, c w ∈ W := P.W_inv_A
  have hWc : commSub W H = W := by
    refine le_antisymm (commSub_le_of_invariant hWH) ?_
    exact sup_le (commI ▸ commSub_mono le_sup_left le_rfl) (commI' ▸ commSub_mono le_sup_right le_rfl)
  set K : Subgroup (MulAut V) := H ⊓ centSub W with hK
  set N : Subgroup (MulAut V) := H ⊓ centSec W Z with hN
  have hKN : K ≤ N := inf_le_inf_left _ (centSub_le_centSec W Z)
  have hNH : N ≤ H := inf_le_left
  have hKn : ∀ g ∈ H, ∀ k ∈ K, g * k * g⁻¹ ∈ K := by
    intro g hg k hk
    refine ⟨H.mul_mem (H.mul_mem hg hk.1) (H.inv_mem hg), fun w hw => ?_⟩
    have : g⁻¹ w ∈ W := hWH g⁻¹ (H.inv_mem hg) w hw
    show g (k (g⁻¹ w)) = w
    rw [hk.2 _ this]; simp
  have hNn : ∀ g ∈ H, ∀ n ∈ N, g * n * g⁻¹ ∈ N := by
    intro g hg n hn
    refine ⟨H.mul_mem (H.mul_mem hg hn.1) (H.inv_mem hg), ?_⟩
    exact centSec_conj hn.2
      (mem_stabSub_of_invariant (hWH g hg) (hWH g⁻¹ (H.inv_mem hg)))
      (fun z hz => by rw [hz g hg]; exact hz)
  have hN2 : ∀ x ∈ N, ∃ k : ℕ, x ^ 2 ^ k ∈ K := by
    intro x hx
    refine ⟨1, H.pow_mem hx.1 _, fun w hw => ?_⟩
    obtain ⟨z, hz, hzw⟩ : ∃ z ∈ Z, x w = z * w := ⟨x w * w⁻¹, hx.2.2 w hw, by group⟩
    have hxz : x z = z := hz x hx.1
    have h1 : (x ^ 2 ^ 1) w = x (x w) := by simp [pow_two, MulAut.mul_apply]
    rw [h1, hzw, map_mul, hxz, hzw]
    have h2 : z * (z * w) = z ^ 2 * w := by rw [sq, mul_assoc]
    rw [h2, hV z, one_mul]
  have hcent : ⁅N, H⁆ ≤ K :=
    twoSection_central hH hCF _ K N rfl hKN hNH (le_normalizer_of_conj hNn)
      (le_normalizer_of_conj hKn) hN2
  have hbn : ∀ h ∈ H, h * b * h⁻¹ * b⁻¹ ∈ N := by
    intro h hh
    refine ⟨?_, ?_⟩
    · have h1 : b * h⁻¹ * b⁻¹ ∈ H := P.conj_mem hb (H.inv_mem hh)
      have : h * b * h⁻¹ * b⁻¹ = h * (b * h⁻¹ * b⁻¹) := by group
      rw [this]
      exact H.mul_mem hh h1
    · have hbc : b ∈ centSec W Z :=
        ⟨mem_stabSub_of_invariant (hWA b hb) (hWA b⁻¹ (A.inv_mem hb)), hbZ⟩
      have hhs : h ∈ stabSub W :=
        mem_stabSub_of_invariant (hWH h hh) (hWH h⁻¹ (H.inv_mem hh))
      exact (centSec W Z).mul_mem
        (centSec_conj hbc hhs (fun z hz => by rw [hz h hh]; exact hz))
        ((centSec W Z).inv_mem hbc)
  have hP := commutator_mem_of_central_section hH hNH hKn hN2 hcent hbn
  have hcom : ∀ h ∈ H, ∀ w ∈ W, b (h w) = h (b w) := by
    intro h hh w hw
    have h1 := (hP h⁻¹ (H.inv_mem hh)).2 (b w) (hWA b hb w hw)
    have h2 : h⁻¹ (b (h w)) = b w := by simpa [MulAut.mul_apply] using h1
    calc b (h w) = h (h⁻¹ (b (h w))) := by simp
      _ = h (b w) := by rw [h2]
  have hfix : ∀ y ∈ commSub W H, b y = y := by
    intro y hy
    refine Subgroup.closure_induction (p := fun y _ => b y = y) ?_ ?_ ?_ ?_ hy
    · rintro _ ⟨h, hh, w, hw, rfl⟩
      obtain ⟨z, hz, hzw⟩ : ∃ z ∈ Z, b w = z * w := ⟨b w * w⁻¹, hbZ w hw, by group⟩
      have e1 : b (h w * w⁻¹) = b (h w) * (b w)⁻¹ := by rw [map_mul, map_inv]
      rw [e1, hcom h hh w hw, hzw, map_mul, hz h hh]
      cgroup
    · simp
    · intro x y _ _ hx hy
      rw [map_mul, hx, hy]
    · intro x _ hx
      rw [map_inv, hx]
  intro w hw
  exact hfix w (by rw [hWc]; exact hw)

end B72Hyp

end CFSG.Quasithin
