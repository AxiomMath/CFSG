module

public import CFSG.Sporadic.Schreier.MathieuOddCoreM22
public import CFSG.Quasithin.Background.A3StructureDefs
public import CFSG.CharacterTheory.Burnside
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.H.Mathieu.M22Link

open CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native CFSG.Blueprint CFSG.Certificates
open CFSG.Sporadic.Mathieu

theorem m22_involution_cover :
    (∀ u, (1 : Equiv.Perm (Fin 22))⁻¹ * u ∈ m22Certificate.originalSubgroup → orderOf u = 2 →
      ∃ r ∈ [m22Rep1], ∃ c ∈ m22Certificate.originalSubgroup, u = c * r * c⁻¹) ∧
    (∀ r ∈ [m22Rep1], (Native.conjClosure 22 (pairTables m22gA m22gB) (pairTables m22gA⁻¹ m22gB⁻¹)
      (toTable r) 2000).1.size ≤ (conjClass m22Certificate.originalSubgroup r).ncard) := by
  have hn : (22 : ℕ) < 2 ^ 32 := by norm_num
  have hQ : ValidSchreier m22Certificate := m22Certificate_check
  obtain ⟨hok, -, -⟩ := m22_oddcore_cover
  obtain ⟨hr1, hro1, -, -, -⟩ := m22_rep_data1
  have hA : m22gA ∈ m22Certificate.originalSubgroup := m22_gens_mem _ (by simp)
  have hB : m22gB ∈ m22Certificate.originalSubgroup := m22_gens_mem _ (by simp)
  rw [m22InvReps_eq] at hok
  exact exists_conj_of_repsOK hn m22Certificate hQ (pairTables_spec hn hA hB) 1
    (fun h hh => by simpa using hh) (by norm_num) [m22Rep1]
    (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr
      exact ⟨by simpa using hr1, hro1⟩) 2000 hok

theorem m22_involution_conj
    {u : Equiv.Perm (Fin 22)} (hu : u ∈ NativeSporadic.M22) (ho : orderOf u = 2) :
    ∃ c ∈ NativeSporadic.M22, u = c * m22Rep1 * c⁻¹ := by
  obtain ⟨hcov, -⟩ := m22_involution_cover
  rw [m22Certificate_originalSubgroup] at hcov
  obtain ⟨r, hr, c, hc, rfl⟩ := hcov u (by simpa using hu) ho
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  subst hr
  exact ⟨c, hc, rfl⟩

theorem m22_involution_centralizer :
    Nat.card (centralizerIn NativeSporadic.M22 m22Rep1) = 384 := by
  obtain ⟨-, hsize⟩ := m22_involution_cover
  obtain ⟨-, hsz, -⟩ := m22_oddcore_cover
  obtain ⟨-, -, hK, hKc, -⟩ := m22_rep_data1
  rw [m22InvReps_eq] at hsz
  simp only [repSizes, List.map_cons, List.map_nil, List.cons.injEq, and_true] at hsz
  have hle := hsize m22Rep1 (by simp)
  rw [hsz] at hle
  have hc := centralizerIn_eq_of_le m22Certificate.originalSubgroup m22Rep1 hK hle
    (by rw [hKc, m22Certificate_originalSubgroup, m22_card])
  rw [← m22Certificate_originalSubgroup, hc, hKc]

variable {X : Type} [Group X]

theorem orderOf_mk_eq_two (hZ : Nat.card ↥(Subgroup.center X) = 3) {a : X} (ha : orderOf a = 2) :
    orderOf (QuotientGroup.mk a : X ⧸ Subgroup.center X) = 2 := by
  have h2 : (QuotientGroup.mk a : X ⧸ Subgroup.center X) ^ 2 = 1 := by
    rw [← QuotientGroup.mk_pow, ← ha, pow_orderOf_eq_one, QuotientGroup.mk_one]
  have h1 : (QuotientGroup.mk a : X ⧸ Subgroup.center X) ≠ 1 := by
    intro h
    rw [QuotientGroup.eq_one_iff] at h
    have h3 : a ^ 3 = 1 := by
      have := pow_card_eq_one' (G := ↥(Subgroup.center X)) (x := ⟨a, h⟩)
      rw [hZ] at this
      exact congrArg Subtype.val this
    have hdvd := orderOf_dvd_of_pow_eq_one h3
    rw [ha] at hdvd
    norm_num at hdvd
  exact orderOf_eq_prime h2 h1

theorem exists_conj_of_orderOf_two
    (hX : CFSG.Quasithin.IsHat X (NativeSporadic.Carrier .M22)) {a b : X} (ha : orderOf a = 2)
    (hb : orderOf b = 2) : ∃ c : X, c * a * c⁻¹ = b := by
  obtain ⟨-, hZ, ⟨e₀⟩⟩ := hX
  let e : X ⧸ Subgroup.center X ≃* ↥NativeSporadic.M22 := e₀
  have hoa := orderOf_mk_eq_two hZ ha
  have hob := orderOf_mk_eq_two hZ hb
  have hea :
      orderOf ((e (QuotientGroup.mk a) : ↥NativeSporadic.M22) : Equiv.Perm (Fin 22)) = 2 := by
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, hoa]
  have heb :
      orderOf ((e (QuotientGroup.mk b) : ↥NativeSporadic.M22) : Equiv.Perm (Fin 22)) = 2 := by
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, hob]
  obtain ⟨c₁, hc₁, h₁⟩ := m22_involution_conj (e (QuotientGroup.mk a)).2 hea
  obtain ⟨c₂, hc₂, h₂⟩ := m22_involution_conj (e (QuotientGroup.mk b)).2 heb
  set d : ↥NativeSporadic.M22 := ⟨c₂ * c₁⁻¹, NativeSporadic.M22.mul_mem hc₂ (inv_mem hc₁)⟩
  have hd : e (QuotientGroup.mk b) = d * e (QuotientGroup.mk a) * d⁻¹ := by
    apply Subtype.ext
    simp only [d, Subgroup.coe_mul, Subgroup.coe_inv, h₁, h₂]
    group
  obtain ⟨c, hc⟩ := QuotientGroup.mk_surjective (e.symm d)
  refine ⟨c, ?_⟩
  have hmod : (QuotientGroup.mk (c * a * c⁻¹) : X ⧸ Subgroup.center X) = QuotientGroup.mk b := by
    apply e.injective
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, hc, map_mul, map_mul,
      map_inv, MulEquiv.apply_symm_apply, hd]
  rw [QuotientGroup.eq] at hmod
  set ζ := (c * a * c⁻¹)⁻¹ * b with hζ
  have hb' : b = c * a * c⁻¹ * ζ := by rw [hζ, mul_inv_cancel_left]
  have hζ3 : ζ ^ 3 = 1 := by
    have := pow_card_eq_one' (G := ↥(Subgroup.center X)) (x := ⟨ζ, hmod⟩)
    rw [hZ] at this
    exact congrArg Subtype.val this
  have hcomm : ∀ x : X, x * ζ = ζ * x := fun x => Subgroup.mem_center_iff.mp hmod x
  have ha2 : a ^ 2 = 1 := by rw [← ha, pow_orderOf_eq_one]
  have hb2 : b ^ 2 = 1 := by rw [← hb, pow_orderOf_eq_one]
  have hζ2 : ζ ^ 2 = 1 := by
    have h1 : b ^ 2 = c * a ^ 2 * c⁻¹ * ζ ^ 2 := by
      rw [hb', pow_two, pow_two, pow_two]
      calc c * a * c⁻¹ * ζ * (c * a * c⁻¹ * ζ) = c * a * c⁻¹ * (ζ * (c * a * c⁻¹)) * ζ := by
            group
        _ = c * a * c⁻¹ * ((c * a * c⁻¹) * ζ) * ζ := by rw [← hcomm (c * a * c⁻¹)]
        _ = c * (a * a) * c⁻¹ * (ζ * ζ) := by group
    rw [ha2, hb2, mul_one, mul_inv_cancel, one_mul] at h1
    exact h1.symm
  have hζ1 : ζ = 1 := by
    calc ζ = ζ ^ 3 * (ζ ^ 2)⁻¹ := by group
      _ = 1 := by rw [hζ2, hζ3, inv_one, mul_one]
  rw [hb', hζ1, mul_one]

theorem card_centralizerIn_conj {M : Type*} [Group M] (H : Subgroup M) {c : M} (hc : c ∈ H)
    (u : M) : Nat.card (centralizerIn H (c * u * c⁻¹)) = Nat.card (centralizerIn H u) := by
  have heq :
      centralizerIn H (c * u * c⁻¹) = (centralizerIn H u).map (MulAut.conj c).toMonoidHom := by
    ext x
    simp only [mem_centralizerIn, Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    constructor
    · rintro ⟨hx, hxu⟩
      refine ⟨c⁻¹ * x * c, ⟨H.mul_mem (H.mul_mem (H.inv_mem hc) hx) hc, ?_⟩, by group⟩
      calc c⁻¹ * x * c * u = c⁻¹ * (x * (c * u * c⁻¹)) * c := by group
        _ = c⁻¹ * ((c * u * c⁻¹) * x) * c := by rw [hxu]
        _ = u * (c⁻¹ * x * c) := by group
    · rintro ⟨y, ⟨hy, hyu⟩, rfl⟩
      refine ⟨H.mul_mem (H.mul_mem hc hy) (H.inv_mem hc), ?_⟩
      calc c * y * c⁻¹ * (c * u * c⁻¹) = c * (y * u) * c⁻¹ := by group
        _ = c * (u * y) * c⁻¹ := by rw [hyu]
        _ = c * u * c⁻¹ * (c * y * c⁻¹) := by group
  rw [heq, Subgroup.card_map_of_injective (MulAut.conj c).injective]

theorem m22_involution_centralizer_card
    {u : Equiv.Perm (Fin 22)}
    (hu : u ∈ NativeSporadic.M22) (ho : orderOf u = 2) :
    Nat.card (centralizerIn NativeSporadic.M22 u) = 384 := by
  obtain ⟨c, hc, rfl⟩ := m22_involution_conj hu ho
  rw [card_centralizerIn_conj _ hc, m22_involution_centralizer]

theorem card_centralizer_dvd
    [Finite X]
    (hX : CFSG.Quasithin.IsHat X (NativeSporadic.Carrier .M22)) {k : X} (hk : orderOf k = 2) :
    Nat.card ↥(Subgroup.centralizer ({k} : Set X)) ∣ 3 * 384 := by
  obtain ⟨-, hZ, ⟨e₀⟩⟩ := hX
  let e : X ⧸ Subgroup.center X ≃* ↥NativeSporadic.M22 := e₀
  set C := Subgroup.centralizer ({k} : Set X) with hC
  let f : ↥C →* X ⧸ Subgroup.center X := (QuotientGroup.mk' (Subgroup.center X)).comp C.subtype
  have hker : Nat.card ↥f.ker ∣ 3 := by
    have hle : f.ker.map C.subtype ≤ Subgroup.center X := by
      rintro _ ⟨x, hx, rfl⟩
      have hx' : (QuotientGroup.mk (x : X) : X ⧸ Subgroup.center X) = 1 := hx
      exact (QuotientGroup.eq_one_iff _).mp hx'
    have h1 := Subgroup.card_dvd_of_le hle
    rwa [Subgroup.card_map_of_injective C.subtype_injective, hZ] at h1
  set kb : X ⧸ Subgroup.center X := QuotientGroup.mk k
  have hrange : f.range ≤ Subgroup.centralizer ({kb} : Set (X ⧸ Subgroup.center X)) := by
    rintro _ ⟨x, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hx := Subgroup.mem_centralizer_singleton_iff.mp x.2
    show (QuotientGroup.mk (x : X) : X ⧸ Subgroup.center X) * QuotientGroup.mk k =
      QuotientGroup.mk k * QuotientGroup.mk (x : X)
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hx]
  have hcent : Nat.card ↥(Subgroup.centralizer ({kb} : Set (X ⧸ Subgroup.center X))) = 384 := by
    have hu : orderOf ((e kb : ↥NativeSporadic.M22) : Equiv.Perm (Fin 22)) = 2 := by
      rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, orderOf_mk_eq_two hZ hk]
    rw [← m22_involution_centralizer_card (e kb).2 hu]
    have h1 : (Subgroup.centralizer ({kb} : Set (X ⧸ Subgroup.center X))).map e.toMonoidHom =
        Subgroup.centralizer ({e kb} : Set ↥NativeSporadic.M22) := by
      ext y
      simp only [Subgroup.mem_map, Subgroup.mem_centralizer_singleton_iff, MulEquiv.coe_toMonoidHom]
      constructor
      · rintro ⟨x, hx, rfl⟩
        rw [← map_mul, hx, map_mul]
      · intro hy
        refine ⟨e.symm y, ?_, MulEquiv.apply_symm_apply _ _⟩
        apply e.injective
        rw [map_mul, map_mul, MulEquiv.apply_symm_apply, hy]
    have h2 : (Subgroup.centralizer ({e kb} : Set ↥NativeSporadic.M22)).map
        NativeSporadic.M22.subtype =
          centralizerIn NativeSporadic.M22 (e kb : Equiv.Perm (Fin 22)) := by
      ext y
      simp only [Subgroup.mem_map, Subgroup.mem_centralizer_singleton_iff, mem_centralizerIn,
        Subgroup.coe_subtype]
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨x.2, by simpa using congrArg Subtype.val hx⟩
      · rintro ⟨hy, hyu⟩
        exact ⟨⟨y, hy⟩, Subtype.ext (by simpa using hyu), rfl⟩
    rw [← h2, Subgroup.card_map_of_injective NativeSporadic.M22.subtype_injective, ← h1,
      Subgroup.card_map_of_injective e.injective]
  have hran : Nat.card ↥f.range ∣ 384 := by
    rw [← hcent]
    exact Subgroup.card_dvd_of_le hrange
  have hsplit := Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv] at hsplit
  rw [hsplit, mul_comm]
  exact Nat.mul_dvd_mul hker hran

theorem isSolvable_centralizer
    [Finite X]
    (hX : CFSG.Quasithin.IsHat X (NativeSporadic.Carrier .M22)) {k : X} (hk : orderOf k = 2) :
    Group.IsSolvable ↥(Subgroup.centralizer ({k} : Set X)) := by
  have hd := card_centralizer_dvd hX hk
  rw [show 3 * 384 = 2 ^ 7 * 3 ^ 2 by norm_num] at hd
  obtain ⟨d₁, d₂, hd₁, hd₂, hd12⟩ := Nat.dvd_mul.mp hd
  obtain ⟨a, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd₁
  obtain ⟨b, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hd₂
  have := Fintype.ofFinite ↥(Subgroup.centralizer ({k} : Set X))
  exact CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow Nat.prime_two
    Nat.prime_three (by norm_num) (by rw [← Nat.card_eq_fintype_card, hd12])

end CFSG.Quasithin.H.Mathieu.M22Link
