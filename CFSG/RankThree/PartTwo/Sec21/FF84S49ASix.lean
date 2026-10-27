module

public import CFSG.RankThree.PartTwo.Sec21.FF84S49AOne
public import CFSG.RankThree.PartTwo.Sec21.FF84S4C6
public import CFSG.RankThree.PartTwo.Sec21.FF84S4A8

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84.S4

open CFSG CFSG.RankThree.PartTwo.Sec21 CFSG.RankThree.PartTwo.Sec21.FF84
open CFSG.RankThree.PartTwo.Sec21.FF84.S3 (P8 A8s)

@[expose] def A_cent_A5_odd_stmt : Prop :=
  ∀ (K' : Subgroup P8), K' ≤ A8s → ∀ (e5 : ↥K' ≃* alternatingGroup (Fin 5)) (c : P8),
    c.IsThreeCycle → c ∈ K' → Odd (Nat.card ↥(CenS K' ⊓ A8s))

open Equiv Equiv.Perm in
private theorem isThreeCycle_dd : dd.IsThreeCycle :=
  card_support_eq_three_iff.mp (by decide +kernel)

variable {G : Type} [Group G] [Finite G] {b : G} {L B K : Subgroup G} {b₁ b₂ : G}

theorem a49_K_perf (eK : ↥K ≃* alternatingGroup (Fin 5)) : ⁅K, K⁆ = K := by
  haveI : Group.IsPerfect (alternatingGroup (Fin 5)) :=
    Group.IsPerfect.mk (commutator_alternatingGroup_eq_top (by simp))
  haveI : Group.IsPerfect ↥K := Group.IsPerfect.ofSurjective (f := eK.symm.toMonoidHom) eK.symm.surjective
  exact Subgroup.commutator_eq_self

theorem a49_conj_K_le_L (hA : A8Model L)
    (h : FF84Post b L B K b₁ b₂) {n : G} (hn : n * b₁ * n⁻¹ = b) {k : G} (hk : k ∈ K) :
    n * k * n⁻¹ ∈ L := by
  obtain ⟨eK⟩ := A49_K_equiv_A5 hA h
  have hperf := a49_K_perf eK
  have hKc : K ≤ Cen b₁ := h.sec.hK.2.2.2.2
  set f : G →* G := (MulAut.conj n).toMonoidHom with hf
  have hX : K.map f ≤ Cen b := by
    rintro _ ⟨y, hy, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hy1 : y * b₁ = b₁ * y := Subgroup.mem_centralizer_singleton_iff.1 (hKc hy)
    have hbn : n⁻¹ * b * n = b₁ := by rw [← hn]; group
    show n * y * n⁻¹ * b = b * (n * y * n⁻¹)
    calc n * y * n⁻¹ * b = n * y * (n⁻¹ * b * n) * n⁻¹ := by group
      _ = n * (y * b₁) * n⁻¹ := by rw [hbn]; group
      _ = n * (b₁ * y) * n⁻¹ := by rw [hy1]
      _ = (n * b₁ * n⁻¹) * (n * y * n⁻¹) := by group
      _ = b * (n * y * n⁻¹) := by rw [hn]
  have hL : K.map f ≤ L := by
    calc K.map f = ⁅K, K⁆.map f := by rw [hperf]
      _ = ⁅K.map f, K.map f⁆ := Subgroup.map_commutator _ _ _
      _ ≤ ⁅Cen b, Cen b⁆ := Subgroup.commutator_mono hX hX
      _ ≤ L := cen_comm_le h
  exact hL ⟨k, hk, rfl⟩

theorem a49_s_not_cenS_L (hA : A8Model L)
    (hodd : A_cent_A5_odd_stmt) (h : FF84Post b L B K b₁ b₂) {s : G} (hs2 : orderOf s = 2)
    (hsc : s ∈ CenS (Subgroup.closure {b₁, b₂})) : s ∉ CenS L := by
  intro hsL
  obtain ⟨-, -, -, -, ⟨n, hn, hnb, hnb₁, hnb₂⟩, -⟩ := h.sec.mono
  obtain ⟨e, -, he₂⟩ := M0_model hA h
  obtain ⟨eK⟩ := A49_K_equiv_A5 hA h
  have hKL := A49_K_le_L h
  have hs1 : b₁ * s = s * b₁ :=
    Subgroup.mem_centralizer_iff.1 hsc b₁ (Subgroup.subset_closure (by simp))
  have hsq : s * s = 1 := mul_self_eq_one_of_orderOf_two hs2
  have hbn : n⁻¹ * b * n = b₁ := by rw [← hnb₁]; group
  set s₁ : G := n * s * n⁻¹ with hs₁def
  have hs₁b : s₁ * b = b * s₁ := by
    calc n * s * n⁻¹ * b = n * s * (n⁻¹ * b * n) * n⁻¹ := by group
      _ = n * (s * b₁) * n⁻¹ := by rw [hbn]; group
      _ = n * (b₁ * s) * n⁻¹ := by rw [hs1]
      _ = (n * b₁ * n⁻¹) * (n * s * n⁻¹) := by group
      _ = b * (n * s * n⁻¹) := by rw [hnb₁]
  have hs₁sq : s₁ * s₁ = 1 := by
    calc n * s * n⁻¹ * (n * s * n⁻¹) = n * (s * s) * n⁻¹ := by group
      _ = 1 := by rw [hsq]; group
  have hs₁L : s₁ ∈ L := sq_mem_L h (Subgroup.mem_centralizer_singleton_iff.2 hs₁b) hs₁sq
  have hs₁1 : s₁ ≠ 1 := by
    intro h1
    apply ne_one_of_orderOf_two hs2
    calc s = n⁻¹ * (n * s * n⁻¹) * n := by group
      _ = 1 := by rw [← hs₁def, h1]; group
  have hKn : ∀ k : ↥K, n * (k : G) * n⁻¹ ∈ L := fun k => a49_conj_K_le_L hA h hnb₁ k.2
  let κ : ↥K →* ↥L :=
    { toFun := fun k => ⟨n * (k : G) * n⁻¹, hKn k⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun x y => Subtype.ext (by
        show n * ((x * y : ↥K) : G) * n⁻¹ = (n * (x : G) * n⁻¹) * (n * (y : G) * n⁻¹)
        rw [Subgroup.coe_mul]; group) }
  have hκinj : Function.Injective κ := by
    intro x y hxy
    have h1 : n * (x : G) * n⁻¹ = n * (y : G) * n⁻¹ := congrArg Subtype.val hxy
    exact Subtype.ext (by simpa using h1)
  let ρ : ↥K →* P8 := (A8s.subtype.comp e.toMonoidHom).comp κ
  have hρinj : Function.Injective ρ := by
    intro x y hxy
    exact hκinj (e.injective (Subtype.ext hxy))
  let K' : Subgroup P8 := ρ.range
  have hK'le : K' ≤ A8s := by
    rintro _ ⟨k, rfl⟩
    exact (e (κ k)).2
  let e5 : ↥K' ≃* alternatingGroup (Fin 5) := (MonoidHom.ofInjective hρinj).symm.trans eK
  have hb₂K : b₂ ∈ K := h.sec.hK.1
  have hdd : dd ∈ K' := by
    refine ⟨⟨b₂, hb₂K⟩, ?_⟩
    exact he₂ (κ ⟨b₂, hb₂K⟩) hnb₂
  have h3 : dd.IsThreeCycle := isThreeCycle_dd
  have hodd' := hodd K' hK'le e5 dd h3 hdd
  have htA : ((e ⟨s₁, hs₁L⟩ : A8s) : P8) ∈ A8s := (e _).2
  have htC : ((e ⟨s₁, hs₁L⟩ : A8s) : P8) ∈ CenS K' := by
    intro y hy
    obtain ⟨k, rfl⟩ := hy
    have hks : (k : G) * s = s * (k : G) :=
      Subgroup.mem_centralizer_iff.1 hsL (k : G) (hKL k.2)
    have hcomm : κ k * ⟨s₁, hs₁L⟩ = ⟨s₁, hs₁L⟩ * κ k := by
      apply Subtype.ext
      show n * (k : G) * n⁻¹ * (n * s * n⁻¹) = n * s * n⁻¹ * (n * (k : G) * n⁻¹)
      calc n * (k : G) * n⁻¹ * (n * s * n⁻¹) = n * ((k : G) * s) * n⁻¹ := by group
        _ = n * (s * (k : G)) * n⁻¹ := by rw [hks]
        _ = n * s * n⁻¹ * (n * (k : G) * n⁻¹) := by group
    have := congrArg (fun z => ((e z : A8s) : P8)) hcomm
    simp only [map_mul, Subgroup.coe_mul] at this
    exact this
  let tt : ↥(CenS K' ⊓ A8s) := ⟨((e ⟨s₁, hs₁L⟩ : A8s) : P8), htC, htA⟩
  have htt : orderOf tt = 2 := by
    refine orderOf_eq_prime ?_ ?_
    · rw [pow_two]
      apply Subtype.ext
      have : (⟨s₁, hs₁L⟩ : ↥L) * ⟨s₁, hs₁L⟩ = 1 := Subtype.ext hs₁sq
      show ((e ⟨s₁, hs₁L⟩ : A8s) : P8) * ((e ⟨s₁, hs₁L⟩ : A8s) : P8) = 1
      calc ((e ⟨s₁, hs₁L⟩ : A8s) : P8) * ((e ⟨s₁, hs₁L⟩ : A8s) : P8)
          = ((e (⟨s₁, hs₁L⟩ * ⟨s₁, hs₁L⟩) : A8s) : P8) := by rw [map_mul]; rfl
        _ = 1 := by rw [this, map_one]; rfl
    · intro h1
      have h2 : ((e ⟨s₁, hs₁L⟩ : A8s) : P8) = 1 := congrArg Subtype.val h1
      have h3 : e ⟨s₁, hs₁L⟩ = 1 := Subtype.ext h2
      have h4 : (⟨s₁, hs₁L⟩ : ↥L) = 1 := e.injective (h3.trans (map_one e).symm)
      exact hs₁1 (congrArg Subtype.val h4)
  have hdvd : 2 ∣ Nat.card ↥(CenS K' ⊓ A8s) := htt ▸ orderOf_dvd_natCard tt
  have hod := Nat.odd_iff.1 hodd'
  omega

theorem P4_inv_outer (hA : A8Model L) (hodd : A_cent_A5_odd_stmt)
    (h : FF84Post b L B K b₁ b₂) {s : G} (hs : orderOf s = 2) (hsb : s * b * s⁻¹ = b⁻¹)
    (hsc : s ∈ CenS (Subgroup.closure {b₁, b₂})) :
    Nonempty (↥(L ⊓ Cen s) ≃* Equiv.Perm (Fin 6)) := by
  obtain ⟨θ, hker, hmem, hsurj, hθ₁, hθ₂⟩ := theta_model hA h.sec
  have hsN : s ∈ Nor L := nor_L_of_inv h hsb
  have hLN : L ≤ Nor L := fun x hx => Subgroup.le_normalizer hx
  have hb₁L : b₁ ∈ L := (Subgroup.mem_inf.1 h.sec.hb₁).2
  have hb₂L : b₂ ∈ L := (Subgroup.mem_inf.1 h.sec.hb₂).2
  have hs1 : b₁ * s = s * b₁ :=
    Subgroup.mem_centralizer_iff.1 hsc b₁ (Subgroup.subset_closure (by simp))
  have hs2 : b₂ * s = s * b₂ :=
    Subgroup.mem_centralizer_iff.1 hsc b₂ (Subgroup.subset_closure (by simp))
  have hsq : s * s = 1 := mul_self_eq_one_of_orderOf_two hs
  set S : ↥(Nor L) := ⟨s, hsN⟩ with hS
  have hSb₁ : S * ⟨b₁, hLN hb₁L⟩ = ⟨b₁, hLN hb₁L⟩ * S := Subtype.ext hs1.symm
  have hSb₂ : S * ⟨b₂, hLN hb₂L⟩ = ⟨b₂, hLN hb₂L⟩ * S := Subtype.ext hs2.symm
  have hθS1 : θ S * cc = cc * θ S := by
    have := congrArg θ hSb₁
    rw [map_mul, map_mul] at this
    rw [hθ₁] at this
    exact this
  have hθS2 : θ S * dd = dd * θ S := by
    have := congrArg θ hSb₂
    rw [map_mul, map_mul] at this
    rw [hθ₂] at this
    exact this
  have hθSsq : θ S * θ S = 1 := by
    rw [← map_mul]
    have : S * S = 1 := Subtype.ext hsq
    rw [this, map_one]
  have hθSne : θ S ≠ 1 := fun h1 => a49_s_not_cenS_L hA hodd h hs hsc ((hker S).1 h1)
  have hθScen : θ S ∈ CenS Pm := (mem_CenS_Pm_iff _).2 ⟨hθS1, hθS2⟩
  have hθSord : orderOf (θ S) = 2 :=
    orderOf_eq_prime (by rw [pow_two]; exact hθSsq) hθSne
  have hθS : θ S = Equiv.swap 6 7 := A_cent_P_inv_involution _ hθScen hθSord
  let φ₀ : ↥L →* P8 := θ.comp (Subgroup.inclusion hLN)
  have hφ₀ : ∀ x : ↥L, φ₀ x = θ ⟨(x : G), hLN x.2⟩ := fun x => rfl
  have hinj : Function.Injective φ₀ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    rw [MonoidHom.mem_ker, hφ₀, hker] at hx
    rw [Subgroup.mem_bot]
    have hxc : x ∈ Subgroup.center ↥L := by
      rw [Subgroup.mem_center_iff]
      intro y
      have := Subgroup.mem_centralizer_iff.1 hx (y : G) y.2
      exact Subtype.ext this
    rw [h.z1] at hxc
    exact Subgroup.mem_bot.1 hxc
  have hmemC : ∀ x : ↥(L ⊓ Cen s), φ₀ (Subgroup.inclusion inf_le_left x) ∈
      Cen (Equiv.swap 6 7) ⊓ A8s := by
    intro x
    refine Subgroup.mem_inf.2 ⟨?_, hmem _⟩
    rw [Subgroup.mem_centralizer_singleton_iff, ← hθS]
    have hxs : (x : G) * s = s * (x : G) :=
      Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 x.2).2
    have hc : (⟨(x : G), hLN (Subgroup.mem_inf.1 x.2).1⟩ : ↥(Nor L)) * S =
        S * ⟨(x : G), hLN (Subgroup.mem_inf.1 x.2).1⟩ := Subtype.ext hxs
    have := congrArg θ hc
    rw [map_mul, map_mul] at this
    exact this
  let ψ : ↥(L ⊓ Cen s) →* ↥(Cen (Equiv.swap 6 7) ⊓ A8s) :=
    (φ₀.comp (Subgroup.inclusion inf_le_left)).codRestrict _ hmemC
  have hψinj : Function.Injective ψ := by
    intro x y hxy
    have h1 : φ₀ (Subgroup.inclusion inf_le_left x) = φ₀ (Subgroup.inclusion inf_le_left y) :=
      congrArg Subtype.val hxy
    have h2 := hinj h1
    exact Subgroup.inclusion_injective _ h2
  have hψsurj : Function.Surjective ψ := by
    rintro ⟨a, haC, haA⟩
    obtain ⟨x, hx⟩ := hsurj a haA
    have hcomm_a : a * Equiv.swap 6 7 = Equiv.swap 6 7 * a :=
      Subgroup.mem_centralizer_singleton_iff.1 haC
    have hxN : (x : G) ∈ Nor L := hLN x.2
    have hsx : s * (x : G)⁻¹ * s⁻¹ ∈ L :=
      (Subgroup.mem_normalizer_iff.1 hsN _).1 (L.inv_mem x.2)
    set c : G := (x : G) * s * (x : G)⁻¹ * s⁻¹ with hc
    have hcL : c ∈ L := by
      have : c = (x : G) * (s * (x : G)⁻¹ * s⁻¹) := by rw [hc]; group
      rw [this]
      exact L.mul_mem x.2 hsx
    have hcN : c ∈ Nor L := hLN hcL
    have hθc : θ ⟨c, hcN⟩ = 1 := by
      have : (⟨c, hcN⟩ : ↥(Nor L)) =
          ⟨(x : G), hxN⟩ * S * ⟨(x : G), hxN⟩⁻¹ * S⁻¹ := Subtype.ext (by
        simp [hc, hS])
      rw [this, map_mul, map_mul, map_mul, map_inv, map_inv, hθS]
      have hx' : θ ⟨(x : G), hxN⟩ = a := hx
      rw [hx']
      calc a * Equiv.swap 6 7 * a⁻¹ * (Equiv.swap 6 7)⁻¹
          = (Equiv.swap 6 7 * a) * a⁻¹ * (Equiv.swap 6 7)⁻¹ := by rw [hcomm_a]
        _ = 1 := by group
    have hcCen : c ∈ CenS L := (hker _).1 hθc
    have hc1 : c = 1 := by
      have hcz : (⟨c, hcL⟩ : ↥L) ∈ Subgroup.center ↥L := by
        rw [Subgroup.mem_center_iff]
        intro y
        exact Subtype.ext (Subgroup.mem_centralizer_iff.1 hcCen (y : G) y.2)
      rw [h.z1] at hcz
      exact congrArg Subtype.val (Subgroup.mem_bot.1 hcz)
    have hxs : (x : G) * s = s * (x : G) := by
      calc (x : G) * s = ((x : G) * s * (x : G)⁻¹ * s⁻¹) * (s * (x : G)) := by group
        _ = s * (x : G) := by rw [← hc, hc1, one_mul]
    refine ⟨⟨(x : G), Subgroup.mem_inf.2 ⟨x.2, Subgroup.mem_centralizer_singleton_iff.2 hxs⟩⟩,
      Subtype.ext ?_⟩
    exact hx
  obtain ⟨e6⟩ := A_cent_P_inv_S6
  exact ⟨(MulEquiv.ofBijective ψ ⟨hψinj, hψsurj⟩).trans e6⟩

theorem P4_S6_cen (hA : A8Model L) (hodd : A_cent_A5_odd_stmt)
    (h : FF84Post b L B K b₁ b₂) {x : G} (hx : orderOf x = 2)
    (hxc : x ∈ CenS (Subgroup.closure {b₁, b₂})) :
    ∃ H : Subgroup G, H ≤ Cen x ∧ Nonempty (↥H ≃* Equiv.Perm (Fin 6)) := by
  obtain ⟨s, hs, -, hsb, hsc⟩ := P4_inv_elt h
  obtain ⟨e6⟩ := P4_inv_outer hA hodd h hs hsb hsc
  obtain ⟨g, -, hg⟩ := P4_one_class hA h hs hx hsc hxc
  have hinj : Function.Injective (MulAut.conj g).toMonoidHom := (MulAut.conj g).injective
  refine ⟨(L ⊓ Cen s).map (MulAut.conj g).toMonoidHom, ?_,
    ⟨(Subgroup.equivMapOfInjective _ _ hinj).symm.trans e6⟩⟩
  rintro _ ⟨y, hy, rfl⟩
  rw [Subgroup.mem_centralizer_singleton_iff]
  have hys : y * s = s * y :=
    Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hy).2
  show g * y * g⁻¹ * x = x * (g * y * g⁻¹)
  rw [← hg]
  calc g * y * g⁻¹ * (g * s * g⁻¹) = g * (y * s) * g⁻¹ := by group
    _ = g * (s * y) * g⁻¹ := by rw [hys]
    _ = g * s * g⁻¹ * (g * y * g⁻¹) := by group

end CFSG.RankThree.PartTwo.Sec21.FF84.S4
