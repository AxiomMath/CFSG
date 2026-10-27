module

public import CFSG.RankThree.PartTwo.Sec21.FF84S49AInv
public import CFSG.RankThree.PartTwo.Sec21.FF84S47Model
public import CFSG.RankThree.PartTwo.Sec21.FF84S3M0

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84.S4

open CFSG CFSG.RankThree.PartTwo.Sec21 CFSG.RankThree.PartTwo.Sec21.FF84
open CFSG.RankThree.PartTwo.Sec21.FF84.S3 (P8 A8s card_inf_of_cycleType3 cycleType_c M0_card_cen)

variable {G : Type} [Group G] [Finite G] {b : G} {L B K : Subgroup G} {b₁ b₂ : G}

private theorem cc_eq_formPerm' : cc = (List.formPerm [0, 1, 2] : P8) := by decide +kernel

theorem A49_card_cen_b₁ (hA : A8Model L)
    (h : FF84Post b L B K b₁ b₂) : Nat.card ↥(L ⊓ Cen b₁) = 180 := by
  obtain ⟨e, he₁, -⟩ := M0_model hA h
  have hb₁ : b₁ ∈ L := (Subgroup.mem_inf.1 h.sec.hb₁).2
  have h1 := M0_card_cen e ⟨b₁, hb₁⟩
  have h2 : ((e ⟨b₁, hb₁⟩ : A8s) : P8) = cc := he₁ ⟨b₁, hb₁⟩ rfl
  change Nat.card ↥(Subgroup.centralizer ({((e ⟨b₁, hb₁⟩ : A8s) : P8)} : Set P8) ⊓ A8s) =
    Nat.card ↥(L ⊓ Cen b₁) at h1
  rw [h2, cc_eq_formPerm'] at h1
  rw [← h1]
  exact card_inf_of_cycleType3 cycleType_c

theorem A49_card_K_le (hA : A8Model L)
    (h : FF84Post b L B K b₁ b₂) : Nat.card K ≤ 60 := by
  obtain ⟨-, -, hsup, hinf, -⟩ := h.sec.hK
  have hZ : Nat.card (Subgroup.zpowers b₁) = 3 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (pow3_of_mem h.sec (mem_b₁ h.sec)) (b₁_ne_one h.sec)
  have h180 := A49_card_cen_b₁ hA h
  have hle1 : Subgroup.zpowers b₁ ≤ L ⊓ Cen b₁ := hsup ▸ le_sup_left
  have hle2 : K ≤ L ⊓ Cen b₁ := hsup ▸ le_sup_right
  let f : Subgroup.zpowers b₁ × K → ↥(L ⊓ Cen b₁) :=
    fun p => ⟨p.1 * p.2, mul_mem (hle1 p.1.2) (hle2 p.2.2)⟩
  have hf : Function.Injective f := by
    rintro ⟨⟨z, hz⟩, ⟨k, hk⟩⟩ ⟨⟨z', hz'⟩, ⟨k', hk'⟩⟩ he
    have he' : z * k = z' * k' := congrArg Subtype.val he
    have hmem : z'⁻¹ * z ∈ Subgroup.zpowers b₁ ⊓ K := by
      refine ⟨Subgroup.mul_mem _ (Subgroup.inv_mem _ hz') hz, ?_⟩
      have : z'⁻¹ * z = k' * k⁻¹ := by
        calc z'⁻¹ * z = z'⁻¹ * (z * k) * k⁻¹ := by group
          _ = z'⁻¹ * (z' * k') * k⁻¹ := by rw [he']
          _ = k' * k⁻¹ := by group
      rw [this]; exact Subgroup.mul_mem _ hk' (Subgroup.inv_mem _ hk)
    rw [hinf, Subgroup.mem_bot] at hmem
    have hzz : z' = z := inv_mul_eq_one.1 hmem
    subst hzz
    have hkk : k = k' := mul_left_cancel he'
    subst hkk
    rfl
  have := Nat.card_le_card_of_injective f hf
  rw [Nat.card_prod, hZ, h180] at this
  omega

theorem A49_K_equiv_A5 (hA : A8Model L)
    (h : FF84Post b L B K b₁ b₂) : Nonempty (↥K ≃* alternatingGroup (Fin 5)) := by
  obtain ⟨-, hKmod, -, -, -⟩ := h.sec.hK
  obtain ⟨e5⟩ := CFSG.ComponentClassification.RankTwoClassical.nonempty_equiv_a5_of_psl hKmod
  have h2 : Nat.card (↥K ⧸ Subgroup.center ↥K) = 60 := by
    rw [Nat.card_congr e5.toEquiv, card_alt5]
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥K)
  have hle := A49_card_K_le hA h
  have hpos : 0 < Nat.card (Subgroup.center ↥K) := Nat.card_pos
  have hZ1 : Nat.card (Subgroup.center ↥K) = 1 := by
    rw [h1, h2] at hle
    omega
  have hZ : Subgroup.center ↥K = ⊥ := Subgroup.eq_bot_of_card_eq _ hZ1
  let φ : ↥K →* alternatingGroup (Fin 5) :=
    e5.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥K))
  have hinj : Function.Injective φ := by
    intro x y hxy
    have : (QuotientGroup.mk' (Subgroup.center ↥K) x) =
        (QuotientGroup.mk' (Subgroup.center ↥K) y) := e5.injective hxy
    have h3 := QuotientGroup.eq.1 this
    rw [hZ, Subgroup.mem_bot] at h3
    exact (inv_mul_eq_one.1 h3)
  have hsurj : Function.Surjective φ :=
    e5.surjective.comp (QuotientGroup.mk'_surjective _)
  exact ⟨MulEquiv.ofBijective φ ⟨hinj, hsurj⟩⟩

theorem A49_K_inv_conj (e : ↥K ≃* alternatingGroup (Fin 5)) {x y : G} (hx : x ∈ K) (hy : y ∈ K)
    (hx2 : x * x = 1) (hy2 : y * y = 1) (hx1 : x ≠ 1) (hy1 : y ≠ 1) :
    ∃ g ∈ K, g * x * g⁻¹ = y := by
  have hxx : (⟨x, hx⟩ * ⟨x, hx⟩ : ↥K) = 1 := Subtype.ext hx2
  have hyy : (⟨y, hy⟩ * ⟨y, hy⟩ : ↥K) = 1 := Subtype.ext hy2
  obtain ⟨g', hg'⟩ := a5_involution_conj (e ⟨x, hx⟩) (e ⟨y, hy⟩)
    (by rw [← map_mul, hxx, map_one])
    (fun h1 => hx1 (congrArg Subtype.val (e.injective (h1.trans (map_one e).symm))))
    (by rw [← map_mul, hyy, map_one])
    (fun h1 => hy1 (congrArg Subtype.val (e.injective (h1.trans (map_one e).symm))))
  refine ⟨((e.symm g' : ↥K) : G), (e.symm g').2, ?_⟩
  have h1 : e (e.symm g' * ⟨x, hx⟩ * (e.symm g')⁻¹) = e ⟨y, hy⟩ := by simpa using hg'
  exact congrArg Subtype.val (e.injective h1)

theorem A49_inv_mem_K (h : FF84Post b L B K b₁ b₂) {z : G} (hzb : z ∈ Cen b)
    (hzb₁ : z ∈ Cen b₁) (hz2 : z * z = 1) : z ∈ K := by
  have hzL : z ∈ L := sq_mem_L h hzb hz2
  have hsup := h.sec.hK.2.2.1
  have : z ∈ Subgroup.zpowers b₁ ⊔ K := by rw [hsup]; exact ⟨hzL, hzb₁⟩
  exact mem_of_sq_one_sup (zpowers_comm_of h.sec.hK.2.2.2.2)
    (zpowers_cube_of (pow3_of_mem h.sec (mem_b₁ h.sec))) this hz2

theorem A49_K_le_L (h : FF84Post b L B K b₁ b₂) : K ≤ L := by
  have hsup := h.sec.hK.2.2.1
  intro k hk
  have : k ∈ Subgroup.zpowers b₁ ⊔ K := Subgroup.mem_sup_right hk
  rw [hsup] at this
  exact this.1

theorem P4_one_class (hA : A8Model L) (h : FF84Post b L B K b₁ b₂)
    {x y : G} (hx : orderOf x = 2) (hy : orderOf y = 2)
    (hxc : x ∈ CenS (Subgroup.closure {b₁, b₂})) (hyc : y ∈ CenS (Subgroup.closure {b₁, b₂})) :
    ∃ g ∈ CenS (Subgroup.closure {b₁, b₂}), g * x * g⁻¹ = y := by
  obtain ⟨-, -, -, -, -, ⟨n, hn, hnb, hnb₁, hnb₂⟩⟩ := h.sec.mono
  obtain ⟨eK⟩ := A49_K_equiv_A5 hA h
  have hb1b : n⁻¹ * b₁ * n = b := by rw [← hnb]; group
  have hb2b : n⁻¹ * b₂ * n = b₁ := by rw [← hnb₁]; group
  have hKL := A49_K_le_L h
  have hKc : K ≤ Cen b₁ := h.sec.hK.2.2.2.2
  have sq1 : ∀ w : G, orderOf w = 2 → w * w = 1 := by
    intro w hw
    have := pow_orderOf_eq_one w
    rwa [hw, pow_two] at this
  have ne1 : ∀ w : G, orderOf w = 2 → w ≠ 1 := by
    intro w hw
    rintro rfl
    simp at hw
  have c1 : ∀ w : G, w ∈ CenS (Subgroup.closure {b₁, b₂}) → b₁ * w = w * b₁ :=
    fun w hw => Subgroup.mem_centralizer_iff.1 hw b₁ (Subgroup.subset_closure (by simp))
  have c2 : ∀ w : G, w ∈ CenS (Subgroup.closure {b₁, b₂}) → b₂ * w = w * b₂ :=
    fun w hw => Subgroup.mem_centralizer_iff.1 hw b₂ (Subgroup.subset_closure (by simp))
  have key : ∀ w : G, orderOf w = 2 → w ∈ CenS (Subgroup.closure {b₁, b₂}) →
      n⁻¹ * w * n ∈ K ∧ n⁻¹ * w * n ≠ 1 := by
    intro w hw hwc
    refine ⟨?_, ?_⟩
    · apply A49_inv_mem_K h
      · rw [Subgroup.mem_centralizer_singleton_iff]
        calc n⁻¹ * w * n * b = n⁻¹ * w * (n * b * n⁻¹) * n := by group
          _ = n⁻¹ * (w * b₁) * n := by rw [hnb]; group
          _ = n⁻¹ * (b₁ * w) * n := by rw [c1 w hwc]
          _ = (n⁻¹ * b₁ * n) * (n⁻¹ * w * n) := by group
          _ = b * (n⁻¹ * w * n) := by rw [hb1b]
      · rw [Subgroup.mem_centralizer_singleton_iff]
        calc n⁻¹ * w * n * b₁ = n⁻¹ * w * (n * b₁ * n⁻¹) * n := by group
          _ = n⁻¹ * (w * b₂) * n := by rw [hnb₁]; group
          _ = n⁻¹ * (b₂ * w) * n := by rw [c2 w hwc]
          _ = (n⁻¹ * b₂ * n) * (n⁻¹ * w * n) := by group
          _ = b₁ * (n⁻¹ * w * n) := by rw [hb2b]
      · calc n⁻¹ * w * n * (n⁻¹ * w * n) = n⁻¹ * (w * w) * n := by group
          _ = 1 := by rw [sq1 w hw]; group
    · intro h1
      apply ne1 w hw
      calc w = n * (n⁻¹ * w * n) * n⁻¹ := by group
        _ = 1 := by rw [h1]; group
  obtain ⟨hx'K, hx'1⟩ := key x hx hxc
  obtain ⟨hy'K, hy'1⟩ := key y hy hyc
  obtain ⟨k, hk, hkxy⟩ := A49_K_inv_conj eK hx'K hy'K
    (by calc n⁻¹ * x * n * (n⁻¹ * x * n) = n⁻¹ * (x * x) * n := by group
          _ = 1 := by rw [sq1 x hx]; group)
    (by calc n⁻¹ * y * n * (n⁻¹ * y * n) = n⁻¹ * (y * y) * n := by group
          _ = 1 := by rw [sq1 y hy]; group) hx'1 hy'1
  have hkb : k * b = b * k :=
    Subgroup.mem_centralizer_singleton_iff.1 (h.sec.hyp.hLC (hKL hk))
  have hkb₁ : k * b₁ = b₁ * k := Subgroup.mem_centralizer_singleton_iff.1 (hKc hk)
  refine ⟨n * k * n⁻¹, ?_, ?_⟩
  · have hle : Subgroup.closure {b₁, b₂} ≤ Cen (n * k * n⁻¹) := by
      rw [Subgroup.closure_le]
      intro z hz
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      have hz' : z = b₁ ∨ z = b₂ := by simpa using hz
      rcases hz' with hz' | hz'
      · rw [hz']
        calc b₁ * (n * k * n⁻¹) = n * (n⁻¹ * b₁ * n) * k * n⁻¹ := by group
          _ = n * (b * k) * n⁻¹ := by rw [hb1b]; group
          _ = n * (k * b) * n⁻¹ := by rw [hkb]
          _ = n * k * (n⁻¹ * b₁ * n) * n⁻¹ := by rw [hb1b]; group
          _ = (n * k * n⁻¹) * b₁ := by group
      · rw [hz']
        calc b₂ * (n * k * n⁻¹) = n * (n⁻¹ * b₂ * n) * k * n⁻¹ := by group
          _ = n * (b₁ * k) * n⁻¹ := by rw [hb2b]; group
          _ = n * (k * b₁) * n⁻¹ := by rw [hkb₁]
          _ = n * k * (n⁻¹ * b₂ * n) * n⁻¹ := by rw [hb2b]; group
          _ = (n * k * n⁻¹) * b₂ := by group
    intro z hz
    exact Subgroup.mem_centralizer_singleton_iff.1 (hle hz)
  · calc n * k * n⁻¹ * x * (n * k * n⁻¹)⁻¹ = n * (k * (n⁻¹ * x * n) * k⁻¹) * n⁻¹ := by group
      _ = n * (n⁻¹ * y * n) * n⁻¹ := by rw [hkxy]
      _ = y := by group

end CFSG.RankThree.PartTwo.Sec21.FF84.S4
