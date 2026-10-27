module

public import CFSG.LocalAnalysis.WeakClosure81.W19Ten
public import CFSG.LocalAnalysis.WeakClosure81.W19TwelveEnd
import CFSG.LocalAnalysis.WeakClosure81.W19CommNeBot
import CFSG.LocalAnalysis.WeakClosure81.W15Defs
public import CFSG.LocalAnalysis.WeakClosure81.SixThirteen

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem pow_mul_mem_coset {O : Subgroup G} {y o : G}
    (hyN : y ∈ Subgroup.normalizer (O : Set G)) (ho : o ∈ O) :
    ∀ n k : ℕ, ∃ o' ∈ O, (y ^ n * o) ^ k = y ^ (n * k) * o' := by
  intro n k
  induction k with
  | zero => exact ⟨1, O.one_mem, by simp⟩
  | succ k ih =>
    obtain ⟨o', ho', h⟩ := ih
    have hynN : y ^ n ∈ Subgroup.normalizer (O : Set G) :=
      (Subgroup.normalizer (O : Set G)).pow_mem hyN n
    have ho'' : (y ^ n)⁻¹ * o' * y ^ n ∈ O :=
      (Subgroup.mem_normalizer_iff''.1 hynN o').mp ho'
    refine ⟨(y ^ n)⁻¹ * o' * y ^ n * o, O.mul_mem ho'' ho, ?_⟩
    rw [pow_succ, h, Nat.mul_succ, pow_add]
    group

private theorem commutatorElement_pow_mem_of_mem {O : Subgroup G} {y u : G}
    (hyN : y ∈ Subgroup.normalizer (O : Set G)) (huy : ⁅u, y⁆ ∈ O) :
    ∀ n : ℕ, ⁅u, y ^ n⁆ ∈ O := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    have hynN : y ^ n ∈ Subgroup.normalizer (O : Set G) :=
      (Subgroup.normalizer (O : Set G)).pow_mem hyN n
    have hmid : y ^ n * ⁅u, y⁆ * (y ^ n)⁻¹ ∈ O :=
      (Subgroup.mem_normalizer_iff.1 hynN ⁅u, y⁆).mp huy
    rw [pow_succ, commutatorElement_mul_right_eq_mul_conj]
    simpa [mul_assoc] using O.mul_mem ih hmid

private theorem commutatorElement_mem_of_mem_coset {O : Subgroup G} {y u z : G}
    (hyN : y ∈ Subgroup.normalizer (O : Set G))
    (huN : u ∈ Subgroup.normalizer (O : Set G))
    (huy : ⁅u, y⁆ ∈ O) (hz : ∃ n : ℕ, ∃ o ∈ O, z = y ^ n * o) :
    ⁅u, z⁆ ∈ O := by
  obtain ⟨n, o, ho, rfl⟩ := hz
  have hpow : ⁅u, y ^ n⁆ ∈ O := commutatorElement_pow_mem_of_mem hyN huy n
  have huo : ⁅u, o⁆ ∈ O := by
    rw [commutatorElement_def]
    exact O.mul_mem ((Subgroup.mem_normalizer_iff.1 huN o).mp ho) (O.inv_mem ho)
  have hynN : y ^ n ∈ Subgroup.normalizer (O : Set G) :=
    (Subgroup.normalizer (O : Set G)).pow_mem hyN n
  have hmid : y ^ n * ⁅u, o⁆ * (y ^ n)⁻¹ ∈ O :=
    (Subgroup.mem_normalizer_iff.1 hynN ⁅u, o⁆).mp huo
  rw [commutatorElement_mul_right_eq_mul_conj]
  simpa [mul_assoc] using O.mul_mem hpow hmid

private theorem mem_centralizerQuot_of_commutatorElement_mem {O : Subgroup G} {y : G}
    {U Z : Subgroup G} (hUO : U ≤ Subgroup.normalizer (O : Set G))
    (hgen : ∀ z ∈ Z, ∃ n : ℕ, ∃ o ∈ O, z = y ^ n * o)
    (hyN : y ∈ Subgroup.normalizer (O : Set G)) {u : G} (hu : u ∈ U)
    (huy : ⁅u, y⁆ ∈ O) : u ∈ centralizerQuot U Z O :=
  mem_centralizerQuot.2 ⟨hu, hUO hu, fun z hz =>
    commutatorElement_mem_of_mem_coset hyN (hUO hu) huy (hgen z hz)⟩

private theorem centralizes_or_inverts_mod
    {U Z O : Subgroup G} {y : G} {p : ℕ}
    (hp : p.Prime) (hyZ : y ∈ Z) (hypow : y ^ p = 1)
    (hyO : ∀ n : ℕ, y ^ n ∈ O → y ^ n = 1)
    (hZO : Z ≤ Subgroup.normalizer (O : Set G))
    (hUO : U ≤ Subgroup.normalizer (O : Set G))
    (hUZ : U ≤ Subgroup.normalizer (Z : Set G))
    (hsq : ∀ u ∈ U, u ^ 2 = 1)
    (hgen : ∀ z ∈ Z, ∃ n : ℕ, ∃ o ∈ O, z = y ^ n * o)
    (hy1 : y ≠ 1) {u : G} (hu : u ∈ U) :
    ⁅u, y⁆ ∈ O ∨ u * y * u⁻¹ * y ∈ O := by
  haveI : Fact p.Prime := ⟨hp⟩
  have horder : orderOf y = p := orderOf_eq_prime hypow hy1
  have hyN : y ∈ Subgroup.normalizer (O : Set G) := hZO hyZ
  have huN : u ∈ Subgroup.normalizer (O : Set G) := hUO hu
  have hu2 : u ^ 2 = 1 := hsq u hu
  have hu2' : u⁻¹ * u⁻¹ = 1 := by
    rw [← mul_inv_rev, ← pow_two, hu2, inv_one]
  have huyZ : u * y * u⁻¹ ∈ Z := (Subgroup.mem_normalizer_iff.1 (hUZ hu) y).mp hyZ
  obtain ⟨n, o, ho, hdecomp⟩ := hgen (u * y * u⁻¹) huyZ
  have hone : y = (y ^ n * o) ^ n * (u * o * u⁻¹) := by
    have hu1 : u * u = 1 := by rw [← pow_two]; exact hu2
    have hzero : u * (u * y * u⁻¹) * u⁻¹ = y := by
      rw [show u * (u * y * u⁻¹) * u⁻¹ = (u * u) * y * (u⁻¹ * u⁻¹) by group,
        hu1, hu2', one_mul, mul_one]
    calc y = u * (u * y * u⁻¹) * u⁻¹ := hzero.symm
      _ = u * (y ^ n * o) * u⁻¹ := by rw [hdecomp]
      _ = (u * y ^ n * u⁻¹) * (u * o * u⁻¹) := by group
      _ = (y ^ n * o) ^ n * (u * o * u⁻¹) := by
          rw [← conj_pow, hdecomp]
  obtain ⟨o', ho', hpow⟩ := pow_mul_mem_coset hyN ho n n
  have huo : u * o * u⁻¹ ∈ O := (Subgroup.mem_normalizer_iff.1 huN o).mp ho
  have htO : o' * (u * o * u⁻¹) ∈ O := O.mul_mem ho' huo
  have honet : y = y ^ (n * n) * (o' * (u * o * u⁻¹)) := by
    calc y = (y ^ n * o) ^ n * (u * o * u⁻¹) := hone
      _ = (y ^ (n * n) * o') * (u * o * u⁻¹) := by rw [hpow]
      _ = y ^ (n * n) * (o' * (u * o * u⁻¹)) := by group
  have hnne : n ≠ 0 := by
    intro hn
    have hyO_mem : y ∈ O := by
      rw [honet, hn]
      simpa using htO
    exact hy1 (by simpa using hyO 1 (by simpa using hyO_mem))
  have hnnpos : 0 < n * n :=
    Nat.mul_pos (Nat.pos_of_ne_zero hnne) (Nat.pos_of_ne_zero hnne)
  have htinv : (o' * (u * o * u⁻¹))⁻¹ ∈ O := O.inv_mem htO
  have hcos : y ^ (n * n) = y * (o' * (u * o * u⁻¹))⁻¹ :=
    eq_mul_inv_of_mul_eq honet.symm
  have hpowmem : y ^ (n * n - 1) ∈ O := by
    have hsplit : y ^ (n * n - 1) * y = y ^ (n * n) := by
      rw [← pow_succ, Nat.sub_add_cancel hnnpos]
    have hval : y ^ (n * n - 1) = y * (o' * (u * o * u⁻¹))⁻¹ * y⁻¹ := by
      rw [eq_mul_inv_of_mul_eq hsplit, hcos]
    rw [hval]
    exact (Subgroup.mem_normalizer_iff.1 hyN _).mp htinv
  have hpow1 : y ^ (n * n - 1) = 1 := hyO _ hpowmem
  have hdvd : p ∣ n * n - 1 := by
    rw [← horder]
    exact orderOf_dvd_of_pow_eq_one hpow1
  have hfac : n * n - 1 = (n - 1) * (n + 1) := by
    rw [mul_self_tsub_one]
    exact Nat.mul_comm _ _
  rcases (Nat.Prime.dvd_mul hp).mp (hfac ▸ hdvd) with hd | hd
  · left
    have hyn1 : y ^ (n - 1) = 1 := by
      rw [← orderOf_dvd_iff_pow_eq_one, horder]
      exact hd
    have hyn : y ^ n = y := by
      rw [← Nat.sub_add_cancel (Nat.pos_of_ne_zero hnne), pow_succ, hyn1, one_mul]
    have hconj : u * y * u⁻¹ = y * o := by rw [hdecomp, hyn]
    have hcomm : ⁅u, y⁆ = y * o * y⁻¹ := by
      rw [commutatorElement_def, hconj]
    rw [hcomm]
    exact (Subgroup.mem_normalizer_iff.1 hyN o).mp ho
  · right
    have hyn1 : y ^ (n + 1) = 1 := by
      rw [← orderOf_dvd_iff_pow_eq_one, horder]
      exact hd
    have hyn : y ^ n = y⁻¹ := by
      have hm : y ^ n * y = 1 := by rw [← pow_succ]; exact hyn1
      exact mul_eq_one_iff_eq_inv.mp hm
    have hconj : u * y * u⁻¹ = y⁻¹ * o := by rw [hdecomp, hyn]
    have hgoal : u * y * u⁻¹ * y = y⁻¹ * o * y := by rw [hconj]
    rw [hgoal]
    exact (Subgroup.mem_normalizer_iff''.1 hyN o).mp ho

private theorem commutatorElement_mul_mem_of_inverts {O : Subgroup G} {y a b : G}
    (hyN : y ∈ Subgroup.normalizer (O : Set G))
    (hbN : b ∈ Subgroup.normalizer (O : Set G))
    (ha : a * y * a⁻¹ * y ∈ O) (hb : b * y * b⁻¹ * y ∈ O) :
    ⁅b * a, y⁆ ∈ O := by
  set ta : G := a * y * a⁻¹ * y with hta
  set tb : G := b * y * b⁻¹ * y with htb
  have hA : a * y * a⁻¹ = ta * y⁻¹ := by rw [hta]; group
  have hB : b * y⁻¹ * b⁻¹ = y * tb⁻¹ := by
    have hB0 : b * y * b⁻¹ = tb * y⁻¹ := by rw [htb]; group
    calc b * y⁻¹ * b⁻¹ = (b * y * b⁻¹)⁻¹ := by group
      _ = (tb * y⁻¹)⁻¹ := by rw [hB0]
      _ = y * tb⁻¹ := by group
  have hconj : b * a * y * (b * a)⁻¹ = (b * ta * b⁻¹) * (y * tb⁻¹) := by
    calc b * a * y * (b * a)⁻¹ = b * (a * y * a⁻¹) * b⁻¹ := by group
      _ = b * (ta * y⁻¹) * b⁻¹ := by rw [hA]
      _ = (b * ta * b⁻¹) * (b * y⁻¹ * b⁻¹) := by group
      _ = (b * ta * b⁻¹) * (y * tb⁻¹) := by rw [hB]
  rw [commutatorElement_def, hconj]
  have h1 : b * ta * b⁻¹ ∈ O := (Subgroup.mem_normalizer_iff.1 hbN ta).mp ha
  have h2 : y * tb⁻¹ * y⁻¹ ∈ O :=
    (Subgroup.mem_normalizer_iff.1 hyN tb⁻¹).mp (O.inv_mem hb)
  rw [show (b * ta * b⁻¹) * (y * tb⁻¹) * y⁻¹
      = (b * ta * b⁻¹) * (y * tb⁻¹ * y⁻¹) by group]
  exact O.mul_mem h1 h2

theorem relIndex_le_two_of_coset_cyclic {p : ℕ} (hp : p.Prime)
    {U Z O : Subgroup G} {y : G} (hyZ : y ∈ Z) (hypow : y ^ p = 1)
    (hyO : ∀ n : ℕ, y ^ n ∈ O → y ^ n = 1)
    (hZO : Z ≤ Subgroup.normalizer (O : Set G))
    (hUO : U ≤ Subgroup.normalizer (O : Set G))
    (hUZ : U ≤ Subgroup.normalizer (Z : Set G))
    (hsq : ∀ u ∈ U, u ^ 2 = 1)
    (hgen : ∀ z ∈ Z, ∃ n : ℕ, ∃ o ∈ O, z = y ^ n * o) :
    (centralizerQuot U Z O).relIndex U ≤ 2 := by
  classical
  let C : Subgroup G := centralizerQuot U Z O
  have hyN : y ∈ Subgroup.normalizer (O : Set G) := hZO hyZ
  have hmemC : ∀ u ∈ U, ⁅u, y⁆ ∈ O → u ∈ C :=
    fun u hu huy => mem_centralizerQuot_of_commutatorElement_mem hUO hgen hyN hu huy
  by_cases hy1 : y = 1
  · have hUC : U ≤ C := fun u hu => hmemC u hu (by
      rw [hy1, commutatorElement_one_right]
      exact O.one_mem)
    have hrel : C.relIndex U = 1 := Subgroup.relIndex_eq_one.2 hUC
    rw [hrel]
    norm_num
  · have hdich : ∀ u ∈ U, ⁅u, y⁆ ∈ O ∨ u * y * u⁻¹ * y ∈ O :=
      fun u hu =>
        centralizes_or_inverts_mod hp hyZ hypow hyO hZO hUO hUZ hsq hgen hy1 hu
    have hdvd : C.relIndex U ∣ 2 := by
      refine (Subgroup.relIndex_dvd_two_iff).mpr ?_
      by_cases hUC : U ≤ C
      · refine ⟨1, U.one_mem, fun b hb => Or.inr ?_⟩
        simpa using hUC hb
      · have hex : ∃ a ∈ U, a ∉ C := by
          by_contra h
          exact hUC fun u hu => by
            by_contra huc
            exact h ⟨u, hu, huc⟩
        obtain ⟨a, haU, haC⟩ := hex
        have hainv : a * y * a⁻¹ * y ∈ O := by
          rcases hdich a haU with h | h
          · exact absurd (hmemC a haU h) haC
          · exact h
        refine ⟨a, haU, fun b hb => ?_⟩
        by_cases hbC : b ∈ C
        · exact Or.inr hbC
        · refine Or.inl ?_
          have hbinv : b * y * b⁻¹ * y ∈ O := by
            rcases hdich b hb with h | h
            · exact absurd (hmemC b hb h) hbC
            · exact h
          refine hmemC (b * a) (U.mul_mem hb haU) ?_
          exact commutatorElement_mul_mem_of_inverts hyN (hUO hb) hainv hbinv
    exact Nat.le_of_dvd (by norm_num) hdvd

namespace MinCex193

variable {D : Data G} {V₀ V : Subgroup G} {p : ℕ} {X : Subgroup G}

private theorem pCore_comm_mem_of_mem_normalizer {H O : Subgroup G} {t : G}
    (htH : t ∈ H) (hHO : H ≤ normalizer (O : Set G)) {o : G} (ho : o ∈ O) :
    ⁅t, o⁆ ∈ O := by
  have htO : t ∈ normalizer (O : Set G) := hHO htH
  have h1 : t * o * t⁻¹ ∈ O := (Subgroup.mem_normalizer_iff.1 htO o).1 ho
  rw [commutatorElement_def]
  exact O.mul_mem h1 (O.inv_mem ho)

private theorem pCore_comm_sup_mem {X O : Subgroup G} {t : G}
    (hXO : X ≤ normalizer (O : Set G))
    (hX : ∀ x ∈ X, ⁅t, x⁆ ∈ O) (hO : ∀ o ∈ O, ⁅t, o⁆ ∈ O) :
    ∀ e ∈ X ⊔ O, ⁅t, e⁆ ∈ O := by
  have hset : ((X ⊔ O : Subgroup G) : Set G) = (X : Set G) * (O : Set G) :=
    Subgroup.coe_mul_of_left_le_normalizer_right X O hXO
  intro e he
  rw [← SetLike.mem_coe, hset] at he
  obtain ⟨x, hx, o, ho, rfl⟩ := he
  have h1 : ⁅t, x * o⁆ = ⁅t, x⁆ * x * ⁅t, o⁆ * x⁻¹ := by
    simp only [commutatorElement_def]
    group
  rw [h1]
  have h2 : x * ⁅t, o⁆ * x⁻¹ ∈ O :=
    (Subgroup.mem_normalizer_iff.1 (hXO hx) _).1 (hO o ho)
  have h3 : ⁅t, x⁆ * x * ⁅t, o⁆ * x⁻¹ = ⁅t, x⁆ * (x * ⁅t, o⁆ * x⁻¹) := by group
  rw [h3]
  exact O.mul_mem (hX x hx) h2

theorem mem_pCoreOf_of_forall_comm_mem (c : MinCex193 D V₀ V p X) {t : G}
    (ht : t ∈ D.T)
    (h : ∀ x ∈ X, ⁅t, x⁆ ∈ pCoreOf 2 (X ⊔ D.T)) :
    t ∈ pCoreOf 2 (X ⊔ D.T) := by
  let H : Subgroup G := X ⊔ D.T
  let O : Subgroup G := pCoreOf 2 (X ⊔ D.T)
  let C : Subgroup G := centralizerQuot H (X ⊔ O) O
  have htH : t ∈ H := Subgroup.mem_sup_right ht
  have hHO : H ≤ normalizer (O : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H
  have hXO : X ≤ normalizer (O : Set G) := fun x hx => hHO (Subgroup.mem_sup_left hx)
  have hCH : H ≤ normalizer (C : Set G) :=
    le_normalizer_centralizerQuot c.le_normalizer_sup_pCoreOf hHO
  have htC : t ∈ C := by
    refine mem_centralizerQuot.2 ⟨htH, hHO htH, ?_⟩
    exact pCore_comm_sup_mem hXO h
      (fun o ho => pCore_comm_mem_of_mem_normalizer htH hHO ho)
  let S : Subgroup G := D.T ⊓ C
  let R : Subgroup G := S ⊔ O
  have hS2 : IsPGroup 2 S := D.sylowM.isPGroup.to_le (show S ≤ D.T from inf_le_left)
  have hO2 : IsPGroup 2 O := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (X ⊔ D.T)
  have hSH : S ≤ H := (show S ≤ D.T from inf_le_left).trans le_sup_right
  have hSN : S ≤ normalizer (O : Set G) := hSH.trans hHO
  have hR2 : IsPGroup 2 R := IsPGroup.to_sup_of_normal_right' hS2 hO2 hSN
  have hXT : X ≤ normalizer (S : Set G) := by
    intro x hx
    refine mem_normalizer_of_conj_mem_fin fun s hs => ?_
    have hxH : x ∈ H := Subgroup.mem_sup_left hx
    have hcomm : ⁅x, s⁆ ∈ O := by
      have h1 : ⁅s, x⁆ ∈ O :=
        (mem_centralizerQuot.1 hs.2).2.2 x (Subgroup.mem_sup_left hx)
      have h2 : ⁅x, s⁆ = ⁅s, x⁆⁻¹ := by
        simp only [commutatorElement_def]
        group
      rw [h2]
      exact O.inv_mem h1
    have hxS : x * s * x⁻¹ ∈ C :=
      (Subgroup.mem_normalizer_iff.1 (hCH hxH) s).1 hs.2
    refine Subgroup.mem_inf.2 ⟨?_, hxS⟩
    have hxs : x * s * x⁻¹ = ⁅x, s⁆ * s := by
      simp only [commutatorElement_def]
      group
    rw [hxs]
    exact D.T.mul_mem (c.hyp.pCoreOf_le_T hcomm) hs.1
  have hDTS : D.T ≤ normalizer (S : Set G) := by
    intro t' ht'
    refine mem_normalizer_of_conj_mem_fin fun s hs => ?_
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.1 (Subgroup.le_normalizer ht') s).1 hs.1
    · exact (Subgroup.mem_normalizer_iff.1 (hCH (Subgroup.mem_sup_right ht')) s).1 hs.2
  have hDTO : D.T ≤ normalizer (O : Set G) := fun t' ht' => hHO (Subgroup.mem_sup_right ht')
  have hXnorm : X ≤ normalizer (R : Set G) := fun x hx =>
    Subgroup.inf_normalizer_le_normalizer_sup S O
      (Subgroup.mem_inf.2 ⟨hXT hx, hXO hx⟩)
  have hDTnorm : D.T ≤ normalizer (R : Set G) := fun t' ht' =>
    Subgroup.inf_normalizer_le_normalizer_sup S O
      (Subgroup.mem_inf.2 ⟨hDTS ht', hDTO ht'⟩)
  have hHN : X ⊔ D.T ≤ normalizer (R : Set G) := sup_le hXnorm hDTnorm
  have hRH : R ≤ X ⊔ D.T :=
    sup_le ((show S ≤ D.T from inf_le_left).trans le_sup_right)
      (CFSG.LieType.BorelTits.pCoreOf_le 2 (X ⊔ D.T))
  have htR : t ∈ R := Subgroup.mem_sup_left (Subgroup.mem_inf.2 ⟨ht, htC⟩)
  exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hRH hHN hR2 htR

private theorem centralizer_singleton_eq_conj_M
    (c : MinCex193 D V₀ V p X) {v u : G} {g : G} (hvV : v ∈ V₀) (hv1 : v ≠ 1)
    (hV₀ : ∀ x ∈ V₀, x = 1 ∨ x = v) (hu : u = g⁻¹ * v * g) :
    Subgroup.centralizer ({u} : Set G) = conjSubgroup D.M g := by
  have huV₀ : u ∈ conjSubgroup V₀ g := by
    rw [hu, mem_conjSubgroup_iff]
    rwa [show g * (g⁻¹ * v * g) * g⁻¹ = v from by group]
  have hu1 : u ≠ 1 := by
    intro h
    apply hv1
    have e : v = g * u * g⁻¹ := by rw [hu]; group
    rw [h] at e
    simpa using e
  refine le_antisymm ?_ ?_
  · intro x hx
    refine centralizer_le_conj_M c.setting c.ne_bot g huV₀ hu1 ?_
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.1 hx u rfl).symm
  · intro x hx
    rw [mem_conjSubgroup_iff] at hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hxm : x = g⁻¹ * (g * x * g⁻¹) * g := by group
    have hvfix := c.conj_eq_of_mem_M hvV hv1 hV₀ hx
    have hcomm : (g * x * g⁻¹) * v = v * (g * x * g⁻¹) :=
      mul_inv_eq_iff_eq_mul.1 hvfix
    calc x * u = g⁻¹ * ((g * x * g⁻¹) * v) * g := by rw [hxm, hu]; group
      _ = g⁻¹ * (v * (g * x * g⁻¹)) * g := by rw [hcomm]
      _ = g⁻¹ * v * (g * x * g⁻¹) * g := by group
      _ = u * x := by rw [hu, hxm]; group

private theorem mem_Z193_of_mem_conj (c : MinCex193 D V₀ V p X) (h2 : Nat.card ↥V₀ = 2)
    {v g : G} (hv : v ∈ V₀) (hgN : g ∈ normalizer (Z193 D V : Set G)) :
    g⁻¹ * v * g ∈ Z193 D V := by
  have h1 : g⁻¹ * v * g ∈ conjSubgroup (Z193 D V) g := by
    rw [mem_conjSubgroup_iff]
    rw [show g * (g⁻¹ * v * g) * g⁻¹ = v from by group]
    exact c.V₀_le_Z193 h2 hv
  rwa [conjSubgroup_eq_iff_mem_normalizer.mpr hgN] at h1

private theorem wClos_le_centralizer_of_mem_Z193 (c : MinCex193 D V₀ V p X)
    {u : G} (huZ : u ∈ Z193 D V) :
    E3.wClos V 1 D.T ≤ Subgroup.centralizer ({u} : Set G) := by
  intro w hw
  rw [Subgroup.mem_centralizer_singleton_iff]
  have huC : u ∈ Subgroup.centralizer (E3.wClos V 1 D.T : Set G) :=
    (c.Z193_le_cClos huZ).2
  exact Subgroup.mem_centralizer_iff.1 huC w hw

private theorem conjSubgroup_le_M_of_is1911 (c : MinCex193 D V₀ V p X)
    (h2 : Nat.card ↥V₀ = 2) {g v u : G} (hgN : g ∈ normalizer (Z193 D V : Set G))
    (hg2 : g ^ 2 ∈ D.M) (hv : v ∈ V₀) (hu : u = g⁻¹ * v * g)
    (hcent : Subgroup.centralizer ({u} : Set G) = conjSubgroup D.M g) :
    conjSubgroup V g ≤ D.M := by
  have huZ : u ∈ Z193 D V := by rw [hu]; exact mem_Z193_of_mem_conj c h2 hv hgN
  have hWle := wClos_le_centralizer_of_mem_Z193 c huZ
  have hVle : V ≤ Subgroup.centralizer ({u} : Set G) := c.V_le_wClos.trans hWle
  intro x hx
  have hxV : g * x * g⁻¹ ∈ V := mem_conjSubgroup_iff.1 hx
  have hxU : g * x * g⁻¹ ∈ conjSubgroup D.M g := by
    rw [← hcent]
    exact hVle hxV
  have hm : g * (g * x * g⁻¹) * g⁻¹ ∈ D.M := mem_conjSubgroup_iff.1 hxU
  have he : g * g * x * (g⁻¹ * g⁻¹) = g * (g * x * g⁻¹) * g⁻¹ := by group
  have hmem : g * g * x * (g⁻¹ * g⁻¹) ∈ D.M := by rwa [he]
  have hinv : g⁻¹ * g⁻¹ ∈ D.M := by
    simpa [pow_two, mul_inv_rev] using D.M.inv_mem hg2
  have hsq : g * g ∈ D.M := by simpa [pow_two] using hg2
  have h1 : (g⁻¹ * g⁻¹) * (g * g * x * (g⁻¹ * g⁻¹)) * (g * g) ∈ D.M :=
    D.M.mul_mem (D.M.mul_mem hinv hmem) hsq
  have he2 : (g⁻¹ * g⁻¹) * (g * g * x * (g⁻¹ * g⁻¹)) * (g * g) = x := by group
  rwa [he2] at h1

private theorem conjSubgroup_le_wClos_of_is1911 (c : MinCex193 D V₀ V p X)
    (h2 : Nat.card ↥V₀ = 2) {g v u : G} (hgN : g ∈ normalizer (Z193 D V : Set G))
    (hg2 : g ^ 2 ∈ D.M) (hv : v ∈ V₀) (hu : u = g⁻¹ * v * g)
    (hcent : Subgroup.centralizer ({u} : Set G) = conjSubgroup D.M g) :
    conjSubgroup V g ≤ E3.wClos V 1 D.T := by
  have huZ : u ∈ Z193 D V := by rw [hu]; exact mem_Z193_of_mem_conj c h2 hv hgN
  have hWle : E3.wClos V 1 D.T ≤ Subgroup.centralizer ({u} : Set G) :=
    wClos_le_centralizer_of_mem_Z193 c huZ
  have hUM : conjSubgroup V g ≤ D.M :=
    conjSubgroup_le_M_of_is1911 c h2 hgN hg2 hv hu hcent
  have hN : Subgroup.normalizer (conjSubgroup V g : Set G) = conjSubgroup D.M g := by
    rw [← E3.conjSubgroup_normalizer, c.setting.normalizer_eq]
  have hWnorm : E3.wClos V 1 D.T ≤ Subgroup.normalizer (conjSubgroup V g : Set G) := by
    rw [hN]
    exact hWle.trans (le_of_eq hcent)
  let Y : Subgroup G := E3.wClos V 1 D.T ⊔ conjSubgroup V g
  have hY : IsPGroup 2 Y :=
    IsPGroup.to_sup_of_normal_right' c.isPGroup_wClos
      (E3.isPGroup_conjSubgroup c.isPGroup_V g) hWnorm
  have hYH : Y ≤ D.M := sup_le (E3.wClos_le 1 D.T |>.trans D.sylowM.le) hUM
  have hS : IsSylowIn 2 D.T D.M := CFSG.ABGLocalTools.isSylowOf_iff.1 D.sylowM
  have hEq : E3.wClos V 1 D.T = E3.wClos V 1 Y :=
    E3.e3_15 hS hYH hY le_sup_left
  have hUY : conjSubgroup V g ≤ E3.wClos V 1 Y :=
    E3.le_wClos_of_mQuot_le c.setting.isElemAbelian g le_sup_right le_rfl
      (k := 1) (by rw [E3.mQuot_self]; omega) (by have := c.three_le_rk; omega)
  rwa [← hEq] at hUY

private theorem conjSubgroup_le_centralizerQuot_of_sq {E F : Subgroup G}
    (hE : Hyp198 D X E F) {g : G}
    (hsq : ∀ g : G, conjSubgroup V g ≤ D.T → ¬ ⁅conjSubgroup V g, E⁆ ≤ F → g ^ 2 ∉ D.M)
    (hg2 : g ^ 2 ∈ D.M) (hUT : conjSubgroup V g ≤ D.T) :
    conjSubgroup V g ≤ centralizerQuot (X ⊔ D.T) E F := by
  have hcomm : ⁅conjSubgroup V g, E⁆ ≤ F := by
    by_contra h
    exact hsq g hUT h hg2
  exact le_centralizerQuot_of_comm_le (hUT.trans le_sup_right) hE.normalizer_F hcomm

private theorem pCoreOf_le_centralizerQuot_of_hyp198 (c : MinCex193 D V₀ V p X)
    {E F : Subgroup G} (hE : Hyp198 D X E F) (hFE : F < E) :
    pCoreOf 2 (X ⊔ D.T) ≤ centralizerQuot (X ⊔ D.T) E F := by
  obtain ⟨W, _, _, _, ρ, ι, -, -, -, -, -, hker, hO⟩ :=
    exists_rep c.hyp.isSolvable hE.E_le hE.isElemAbelian hFE hE.normalizer_E
      hE.normalizer_F hE.irreducible
  intro n hn
  have hnH : n ∈ X ⊔ D.T := CFSG.LieType.BorelTits.pCoreOf_le 2 _ hn
  exact (hker ⟨n, hnH⟩).1 (hO ⟨n, hnH⟩ hn)

private theorem isCyclic_inf_centralizerQuot (c : MinCex193 D V₀ V p X)
    {E F : Subgroup G} (hE : Hyp198 D X E F) (hXE : ¬ ⁅X, E⁆ ≤ F) :
    IsCyclic ↥(X ⊓ centralizerQuot (X ⊔ D.T) E F) := by
  let K : Subgroup G := centralizerQuot (X ⊔ D.T) E F
  let L : Subgroup G := K ⊔ D.T
  have hKH : K ≤ X ⊔ D.T := centralizerQuot_le (X ⊔ D.T) E F
  have hNK : X ⊔ D.T ≤ Subgroup.normalizer (K : Set G) :=
    le_normalizer_centralizerQuot hE.normalizer_E hE.normalizer_F
  have hLH : L ≤ X ⊔ D.T := sup_le hKH le_sup_right
  by_cases hL : L = X ⊔ D.T
  · have hsup : D.T ⊔ K = X ⊔ D.T := by rw [sup_comm]; exact hL
    have htwo : ∀ y ∈ X ⊔ D.T, ∃ k : ℕ, y ^ 2 ^ k ∈ K :=
      CFSG.Quasithin.B6.isTwoQuotient_of_sup_eq D.sylowM.isPGroup hNK hsup
    have hres : twoResidual (X ⊔ D.T) ≤ K :=
      twoResidual_le_of_isTwoQuotient hKH hNK htwo
    have hXK : X ≤ K := c.X_le_twoResidual.trans hres
    exact absurd (Subgroup.commutator_le.2 fun x hx e he =>
      (mem_centralizerQuot.1 (hXK hx)).2.2 e he) hXE
  · have hlt : L < X ⊔ D.T := lt_of_le_of_ne hLH hL
    exact c.cyclic L le_sup_right hlt (X ⊓ K)
      (inf_le_right.trans le_sup_left) (c.hyp.isPGroup.to_le inf_le_left)

private theorem conj_u_mem_M_of_relIndex (c : MinCex193 D V₀ V p X)
    (h2 : Nat.card ↥V₀ = 2) {g v u : G}
    (hgN : g ∈ normalizer (Z193 D V : Set G)) (hv : v ∈ V₀)
    (hu : u = g⁻¹ * v * g)
    (hu2 : (conjSubgroup V g ⊓ pCoreOf 2 (X ⊔ D.T)).relIndex (conjSubgroup V g) ≤ 2)
    {h : G} (hh : h ∈ X ⊔ D.T) :
    (g * h) * u * (g * h)⁻¹ ∈ D.M := by
  let U : Subgroup G := conjSubgroup V g
  let O : Subgroup G := pCoreOf 2 (X ⊔ D.T)
  have huZ : u ∈ Z193 D V := by rw [hu]; exact mem_Z193_of_mem_conj c h2 hv hgN
  have huC : u ∈ Subgroup.centralizer (E3.wClos V 1 D.T : Set G) :=
    (c.Z193_le_cClos huZ).2
  have hBleW : conjSubgroup (U ⊓ O) h ≤ E3.wClos V 1 D.T := by
    have hOn : X ⊔ D.T ≤ Subgroup.normalizer (O : Set G) :=
      CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X ⊔ D.T)
    have hOh : conjSubgroup O h = O := conjSubgroup_eq_iff_mem_normalizer.mpr (hOn hh)
    have hBhT : conjSubgroup (U ⊓ O) h ≤ D.T := by
      refine (E3.conjSubgroup_mono_left h inf_le_right).trans ?_
      rw [hOh]
      exact c.hyp.pCoreOf_le_T
    have hBhV : conjSubgroup (U ⊓ O) h ≤ conjSubgroup V (g * h) := by
      rw [← CFSG.Quasithin.conjSubgroup_conjSubgroup V g h]
      exact E3.conjSubgroup_mono_left h inf_le_left
    have hm : E3.mQuot (conjSubgroup V (g * h)) (conjSubgroup (U ⊓ O) h) ≤ 1 := by
      rw [show conjSubgroup V (g * h) = conjSubgroup U h from
        (CFSG.Quasithin.conjSubgroup_conjSubgroup V g h).symm]
      rw [E3.mQuot_conjSubgroup]
      have hu2' : (U ⊓ O).relIndex U ≤ 2 := hu2
      have hpos : 0 < (U ⊓ O).relIndex U := Nat.pos_of_ne_zero (E3.relIndex_ne_zero' U _)
      have hcases : (U ⊓ O).relIndex U = 1 ∨ (U ⊓ O).relIndex U = 2 := by omega
      rcases hcases with h1 | h1 <;> simp [E3.mQuot, h1]
    exact E3.le_wClos_of_mQuot_le c.setting.isElemAbelian (g := g * h) hBhT hBhV hm
      (by have := c.three_le_rk; omega)
  have hBleC : conjSubgroup (U ⊓ O) h ≤ Subgroup.centralizer ({u} : Set G) :=
    hBleW.trans (wClos_le_centralizer_of_mem_Z193 c huZ)
  have huCB : u ∈ Subgroup.centralizer (conjSubgroup (U ⊓ O) h : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact (Subgroup.mem_centralizer_iff.1 (hBleC hb) u rfl).symm
  let B0 : Subgroup G := conjSubgroup (U ⊓ O) g⁻¹
  have hB0V : B0 ≤ V := by
    have h1 : conjSubgroup U g⁻¹ = V := E3.conjSubgroup_conj_inv V g
    rw [show B0 = conjSubgroup (U ⊓ O) g⁻¹ from rfl]
    exact (E3.conjSubgroup_mono_left g⁻¹ inf_le_left).trans (le_of_eq h1)
  have hmB0 : E3.mQuot V B0 ≤ 1 := by
    have h1 : E3.mQuot V B0 = E3.mQuot U (U ⊓ O) := by
      rw [show B0 = conjSubgroup (U ⊓ O) g⁻¹ from rfl,
        ← E3.conjSubgroup_conj_inv V g]
      exact E3.mQuot_conjSubgroup U (U ⊓ O) g⁻¹
    rw [h1]
    have hu2' : (U ⊓ O).relIndex U ≤ 2 := hu2
    have hpos : 0 < (U ⊓ O).relIndex U := Nat.pos_of_ne_zero (E3.relIndex_ne_zero' U _)
    have hcases : (U ⊓ O).relIndex U = 1 ∨ (U ⊓ O).relIndex U = 2 := by omega
    rcases hcases with h2' | h2' <;> simp [E3.mQuot, h2']
  have hC0M : Subgroup.centralizer (B0 : Set G) ≤ D.M := by
    have hH := Hyp15.of_setting c.setting c.ne_bot
    exact FourteenTwo.fourteen_three hH.h6.elemAbelian hH.h6.le h2
      hH.h6.normalizer_eq.symm.le hH.normalizer₀.symm (hH.h6.conjGenerated hH.ne_bot)
      hH.s14c hH.exists_cTilde_not_le B0 hB0V hmB0
  have hBeq : conjSubgroup B0 (g * h) = conjSubgroup (U ⊓ O) h := by
    rw [show B0 = conjSubgroup (U ⊓ O) g⁻¹ from rfl,
      CFSG.Quasithin.conjSubgroup_conjSubgroup]
    rw [show g⁻¹ * (g * h) = h from by group]
  have hconjC : conjSubgroup (Subgroup.centralizer (B0 : Set G)) (g * h) =
      Subgroup.centralizer (conjSubgroup B0 (g * h) : Set G) :=
    E3.conjSubgroup_centralizer B0 (g * h)
  have hmem : (g * h) * u * (g * h)⁻¹ ∈ Subgroup.centralizer (B0 : Set G) := by
    have h1 : u ∈ conjSubgroup (Subgroup.centralizer (B0 : Set G)) (g * h) := by
      rw [hconjC, hBeq]
      exact huCB
    rwa [mem_conjSubgroup_iff] at h1
  exact hC0M hmem

private theorem comm_mem_pCoreOf_of_centralizes (c : MinCex193 D V₀ V p X)
    {E F : Subgroup G} (hE : Hyp198 D X E F) {g u' : G}
    (hUT : conjSubgroup V g ≤ D.T)
    (hUK : conjSubgroup V g ≤ centralizerQuot (X ⊔ D.T) E F)
    (hgU : u' ∈ conjSubgroup V g) (hu'2 : u' ^ 2 = 1)
    (hcent : ∀ z ∈ centralizerQuot (X ⊔ D.T) E F ⊓ (X ⊔ pCoreOf 2 (X ⊔ D.T)),
      ⁅u', z⁆ ∈ pCoreOf 2 (X ⊔ D.T))
    {x : G} (hx : x ∈ X) :
    ⁅u', x⁆ ∈ pCoreOf 2 (X ⊔ D.T) := by
  let O : Subgroup G := pCoreOf 2 (X ⊔ D.T)
  let K : Subgroup G := centralizerQuot (X ⊔ D.T) E F
  have hOn : X ⊔ D.T ≤ Subgroup.normalizer (O : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X ⊔ D.T)
  have hKn : X ⊔ D.T ≤ Subgroup.normalizer (K : Set G) := by
    change X ⊔ D.T ≤ Subgroup.normalizer
      (centralizerQuot (X ⊔ D.T) E F : Set G)
    exact le_normalizer_centralizerQuot (H := X ⊔ D.T) (E := E) (F := F)
      hE.normalizer_E hE.normalizer_F
  have hu'H : u' ∈ X ⊔ D.T := (le_sup_right : D.T ≤ X ⊔ D.T) (hUT hgU)
  have hxH : x ∈ X ⊔ D.T := Subgroup.mem_sup_left hx
  have hcK : ⁅u', x⁆ ∈ K := by
    have h1 : x * u'⁻¹ * x⁻¹ ∈ K :=
      (Subgroup.mem_normalizer_iff.1 (hKn hxH) u'⁻¹).1 (K.inv_mem (hUK hgU))
    have he : u' * x * u'⁻¹ * x⁻¹ = u' * (x * u'⁻¹ * x⁻¹) := by group
    rw [commutatorElement_def, he]
    exact K.mul_mem (hUK hgU) h1
  have hcXO : ⁅u', x⁆ ∈ X ⊔ O := by
    have h1 : u' * x * u'⁻¹ ∈ X ⊔ O :=
      (Subgroup.mem_normalizer_iff.1 (c.le_normalizer_sup_pCoreOf hu'H) x).1
        (Subgroup.mem_sup_left hx)
    rw [commutatorElement_def]
    exact (X ⊔ O).mul_mem h1 (Subgroup.mem_sup_left (X.inv_mem hx))
  set c' : G := ⁅u', x⁆ with hc'
  have hsq : u' * u' = 1 := by rw [← pow_two]; exact hu'2
  have hu'inv : u'⁻¹ = u' := inv_eq_of_mul_eq_one_right hsq
  have hc'def : c' = u' * x * u' * x⁻¹ := by rw [hc', commutatorElement_def, hu'inv]
  have hword : u' * c' * u' * c' = 1 := by
    calc u' * c' * u' * c'
        = (u' * u') * x * u' * x⁻¹ * (u' * u') * x * u' * x⁻¹ := by
          rw [hc'def]; group
      _ = 1 * x * u' * x⁻¹ * 1 * x * u' * x⁻¹ := by rw [hsq]
      _ = x * (u' * u') * x⁻¹ := by group
      _ = 1 := by rw [hsq]; group
  have hinv : u' * c' * u'⁻¹ = c'⁻¹ := by
    rw [hu'inv]
    exact mul_eq_one_iff_eq_inv.1 hword
  have hcomm : ⁅u', c'⁆ = c'⁻¹ * c'⁻¹ := by
    rw [commutatorElement_def, hinv]
  have hc'2O : c' ^ 2 ∈ O := by
    have h1 := hcent c' (Subgroup.mem_inf.2 ⟨hcK, hcXO⟩)
    rw [hcomm] at h1
    have he : (c'⁻¹ * c'⁻¹)⁻¹ = c' ^ 2 := by group
    rw [← he]
    exact O.inv_mem h1
  have hperm : (X : Set G) * (O : Set G) = (O : Set G) * (X : Set G) :=
    Subgroup.set_mul_normalizer_comm (X : Set G) O
      (fun z hz => hOn (Subgroup.mem_sup_left hz))
  have hset : ((X ⊔ O : Subgroup G) : Set G) = (X : Set G) * (O : Set G) :=
    W19Aux.coe_sup_eq_mul_of_perm hperm
  have hmem : c' ∈ (X : Set G) * (O : Set G) := by
    rw [← hset]
    exact hcXO
  obtain ⟨x₁, hx₁X, o₁, ho₁O, hx₁o₁⟩ := Set.mem_mul.mp hmem
  have ho' : x₁⁻¹ * o₁ * x₁ ∈ O := by
    have hx₁N : x₁⁻¹ ∈ Subgroup.normalizer (O : Set G) :=
      (Subgroup.normalizer (O : Set G)).inv_mem (hOn (Subgroup.mem_sup_left hx₁X))
    simpa using (Subgroup.mem_normalizer_iff.1 hx₁N o₁).1 ho₁O
  have hx₁2O : x₁ ^ 2 ∈ O := by
    have hsq : (x₁ * o₁) ^ 2 ∈ O := by rw [hx₁o₁]; exact hc'2O
    have he : (x₁ * o₁) ^ 2 = x₁ ^ 2 * (x₁⁻¹ * o₁ * x₁) * o₁ := by
      rw [pow_two]
      group
    rw [he] at hsq
    set c₂ : G := (x₁⁻¹ * o₁ * x₁) * o₁ with hc₂
    have hc2 : c₂ ∈ O := O.mul_mem ho' ho₁O
    have hsq' : x₁ ^ 2 * c₂ ∈ O := by simpa [hc₂, mul_assoc] using hsq
    have h1 : (x₁ ^ 2 * c₂) * c₂⁻¹ ∈ O := O.mul_mem hsq' (O.inv_mem hc2)
    rwa [show (x₁ ^ 2 * c₂) * c₂⁻¹ = x₁ ^ 2 from by group] at h1
  have hx₁2bot : x₁ ^ 2 = 1 := by
    have hmem : x₁ ^ 2 ∈ X ⊓ O :=
      Subgroup.mem_inf.2 ⟨X.pow_mem hx₁X 2, hx₁2O⟩
    rw [show X ⊓ O = X ⊓ pCoreOf 2 (X ⊔ D.T) from rfl,
      c.hyp.inf_pCoreOf_eq_bot, Subgroup.mem_bot] at hmem
    exact hmem
  have hx₁bot : x₁ ∈ (⊥ : Subgroup G) :=
    E1.mem_of_pow_mem_two_p c.hyp.prime c.hyp.odd (N := ⊥) (k := 1) (j := 1)
      (by rw [pow_one]; exact c.hyp.exponent x₁ hx₁X)
      (by rw [pow_one, hx₁2bot]; exact Subgroup.one_mem _)
  rw [Subgroup.mem_bot] at hx₁bot
  rw [← hx₁o₁, hx₁bot, one_mul]
  exact ho₁O

private theorem step8_relIndex (c : MinCex193 D V₀ V p X)
    {E F : Subgroup G} (hE : Hyp198 D X E F) (hFE : F < E)
    (hXE : ¬ ⁅X, E⁆ ≤ F) {g : G}
    (hUT : conjSubgroup V g ≤ D.T)
    (hUK : conjSubgroup V g ≤ centralizerQuot (X ⊔ D.T) E F) :
    (conjSubgroup V g ⊓ pCoreOf 2 (X ⊔ D.T)).relIndex (conjSubgroup V g) ≤ 2 := by
  let U : Subgroup G := conjSubgroup V g
  let H : Subgroup G := X ⊔ D.T
  let O : Subgroup G := pCoreOf 2 H
  let K : Subgroup G := centralizerQuot H E F
  let Z₀ : Subgroup G := K ⊓ (X ⊔ O)
  have hOK : O ≤ K := pCoreOf_le_centralizerQuot_of_hyp198 c hE hFE
  have hKH : K ≤ H := centralizerQuot_le H E F
  have hHO : H ≤ Subgroup.normalizer (O : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H
  have hHXO : H ≤ Subgroup.normalizer ((X ⊔ O : Subgroup G) : Set G) :=
    c.le_normalizer_sup_pCoreOf
  have hHKn : H ≤ Subgroup.normalizer (K : Set G) := by
    change H ≤ Subgroup.normalizer (centralizerQuot H E F : Set G)
    exact le_normalizer_centralizerQuot hE.normalizer_E hE.normalizer_F
  have hUH : U ≤ H := hUT.trans le_sup_right
  have hUO : U ≤ Subgroup.normalizer (O : Set G) := hUH.trans hHO
  have hUKn : U ≤ Subgroup.normalizer (K : Set G) := hUH.trans hHKn
  have hUXOn : U ≤ Subgroup.normalizer ((X ⊔ O : Subgroup G) : Set G) :=
    hUH.trans hHXO
  have hUZ₀ : U ≤ Subgroup.normalizer (Z₀ : Set G) := by
    change U ≤ Subgroup.normalizer ((K ⊓ (X ⊔ O) : Subgroup G) : Set G)
    exact (le_inf hUKn hUXOn).trans Subgroup.inf_normalizer_le_normalizer_inf
  have hZ₀H : Z₀ ≤ H :=
    (inf_le_right : Z₀ ≤ X ⊔ O).trans
      (sup_le le_sup_left (c.hyp.pCoreOf_le_T.trans le_sup_right))
  have hZ₀O : Z₀ ≤ Subgroup.normalizer (O : Set G) := hZ₀H.trans hHO
  have hXO_perm : (X : Set G) * (O : Set G) = (O : Set G) * (X : Set G) :=
    Subgroup.set_mul_normalizer_comm (X : Set G) O
      (fun z hz => hHO (Subgroup.mem_sup_left hz))
  have hXO_set : ((X ⊔ O : Subgroup G) : Set G) = (X : Set G) * (O : Set G) :=
    W19Aux.coe_sup_eq_mul_of_perm hXO_perm
  haveI hcyc : IsCyclic ↥(X ⊓ K) := isCyclic_inf_centralizerQuot c hE hXE
  obtain ⟨y0, hygen0⟩ := IsCyclic.exists_monoid_generator (α := ↥(X ⊓ K))
  let y : G := (y0 : G)
  have hyX : y ∈ X := (Subgroup.mem_inf.1 y0.2).1
  have hyK : y ∈ K := (Subgroup.mem_inf.1 y0.2).2
  have hyZ₀ : y ∈ Z₀ := Subgroup.mem_inf.2 ⟨hyK, Subgroup.mem_sup_left hyX⟩
  have hygen : ∀ z ∈ X ⊓ K, ∃ n : ℕ, z = y ^ n := by
    intro z hz
    obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff (⟨z, hz⟩ : ↥(X ⊓ K)) y0).1
      (hygen0 ⟨z, hz⟩)
    exact ⟨n, by simpa [y] using (congrArg Subtype.val hn).symm⟩
  have hgen : ∀ z ∈ Z₀, ∃ n : ℕ, ∃ o ∈ O, z = y ^ n * o := by
    intro z hz
    obtain ⟨hzK, hzXO⟩ := Subgroup.mem_inf.1 hz
    have hmem : z ∈ (X : Set G) * (O : Set G) := by
      rw [← hXO_set]
      exact hzXO
    obtain ⟨x, hxX, o, hoO, hxzo⟩ := Set.mem_mul.mp hmem
    have hxK : x ∈ K := by
      have h1 : x = z * o⁻¹ := by rw [← hxzo]; group
      rw [h1]
      exact K.mul_mem hzK (K.inv_mem (hOK hoO))
    obtain ⟨n, hn⟩ := hygen x (Subgroup.mem_inf.2 ⟨hxX, hxK⟩)
    refine ⟨n, o, hoO, ?_⟩
    rw [← hxzo, hn]
  have hyO : ∀ n : ℕ, y ^ n ∈ O → y ^ n = 1 := by
    intro n hn
    have hmem : y ^ n ∈ X ⊓ O :=
      Subgroup.mem_inf.2 ⟨X.pow_mem hyX n, hn⟩
    rw [show X ⊓ O = X ⊓ pCoreOf 2 (X ⊔ D.T) from rfl,
      c.hyp.inf_pCoreOf_eq_bot, Subgroup.mem_bot] at hmem
    exact hmem
  have hsq : ∀ u ∈ U, u ^ 2 = 1 := fun u hu =>
    (E3.isElemAbelian_conjSubgroup c.setting.isElemAbelian g).2 u hu
  have hCrel : (centralizerQuot U Z₀ O).relIndex U ≤ 2 :=
    relIndex_le_two_of_coset_cyclic c.hyp.prime hyZ₀ (c.hyp.exponent y hyX) hyO hZ₀O hUO
      hUZ₀ hsq hgen
  have hCle : centralizerQuot U Z₀ O ≤ U ⊓ O := by
    intro u' hu'
    have hu'U : u' ∈ U := (mem_centralizerQuot.1 hu').1
    refine Subgroup.mem_inf.2 ⟨hu'U, ?_⟩
    refine mem_pCoreOf_of_forall_comm_mem c (hUT hu'U) fun x hx => ?_
    exact comm_mem_pCoreOf_of_centralizes c hE hUT hUK hu'U (hsq u' hu'U)
      (fun z hz => (mem_centralizerQuot.1 hu').2.2 z hz) hx
  have hle : (U ⊓ O).relIndex U ≤ (centralizerQuot U Z₀ O).relIndex U :=
    Subgroup.relIndex_le_of_le_left hCle (E3.relIndex_ne_zero' U _)
  exact hle.trans hCrel

private theorem eq_one_or_eq_u_of_mem_conj (h2 : Nat.card ↥V₀ = 2) {g v u : G} (hv : v ∈ V₀)
    (hv1 : v ≠ 1)
    (hu : u = g⁻¹ * v * g) {x : G} (hx : x ∈ conjSubgroup V₀ g) :
    x = 1 ∨ x = u := by
  have huU : u ∈ conjSubgroup V₀ g := by
    rw [hu, mem_conjSubgroup_iff]
    rwa [show g * (g⁻¹ * v * g) * g⁻¹ = v from by group]
  have hu1 : u ≠ 1 := by
    intro h
    apply hv1
    have e : v = g * u * g⁻¹ := by rw [hu]; group
    rw [h] at e
    simpa using e
  have hcard : Nat.card ↥(conjSubgroup V₀ g) = 2 := by
    rw [E3.card_conjSubgroup, h2]
  obtain ⟨a, ha1, ha⟩ := (Nat.card_eq_two_iff' (1 : ↥(conjSubgroup V₀ g))).1 hcard
  by_cases hx1 : x = 1
  · exact Or.inl hx1
  · refine Or.inr ?_
    have hxa : (⟨x, hx⟩ : ↥(conjSubgroup V₀ g)) = a := ha ⟨x, hx⟩ (by simpa using hx1)
    have hua : (⟨u, huU⟩ : ↥(conjSubgroup V₀ g)) = a := ha ⟨u, huU⟩ (by simpa using hu1)
    calc x = ((⟨x, hx⟩ : ↥(conjSubgroup V₀ g)) : G) := rfl
      _ = (a : G) := congrArg Subtype.val hxa
      _ = u := (congrArg Subtype.val hua).symm

private theorem le_conj_M_mul_of_is1911 (c : MinCex193 D V₀ V p X)
    (h2 : Nat.card ↥V₀ = 2) {I : Subgroup G}
    {g v u : G} (hv : v ∈ V₀) (hv1 : v ≠ 1)
    (hV₀ : ∀ x ∈ V₀, x = 1 ∨ x = v) (hu : u = g⁻¹ * v * g)
    (hgN : g ∈ normalizer (Z193 D V : Set G))
    (hIeq : V₀ ⊔ conjSubgroup V₀ g = I) {k : G} (hk : k ∈ X ⊔ D.T)
    (hkuM : (g * k) * u * (g * k)⁻¹ ∈ D.M) :
    I ≤ conjSubgroup D.M (g * k) := by
  have hV₀_le : V₀ ≤ conjSubgroup D.M (g * k) := by
    intro x hx
    rw [mem_conjSubgroup_iff]
    by_cases hx1 : x = 1
    · rw [hx1]
      simp
    · have hxv : x = v := by
        rcases hV₀ x hx with h | h
        · exact absurd h hx1
        · exact h
      have hkx : k * v * k⁻¹ = v :=
        c.conj_eq_of_mem_M hv hv1 hV₀ (c.hyp.le_M hk)
      have hgx : g * v * g⁻¹ ∈ D.M :=
        mem_conjSubgroup_iff.1 (c.V₀_le_conj_M h2 hgN hv)
      rw [hxv]
      have he : (g * k) * v * (g * k)⁻¹ = g * v * g⁻¹ := by
        calc (g * k) * v * (g * k)⁻¹ = g * (k * v * k⁻¹) * g⁻¹ := by group
          _ = g * v * g⁻¹ := by rw [hkx]
      rw [he]
      exact hgx
  have hU₀_le : conjSubgroup V₀ g ≤ conjSubgroup D.M (g * k) := by
    intro x hx
    rcases eq_one_or_eq_u_of_mem_conj h2 hv hv1 hu hx with h | h
    · rw [h, mem_conjSubgroup_iff]
      simp
    · rw [h, mem_conjSubgroup_iff]
      exact hkuM
  rw [← hIeq]
  exact sup_le hV₀_le hU₀_le

private theorem comm_of_mem_I_of_is1911 (c : MinCex193 D V₀ V p X)
    (h2 : Nat.card ↥V₀ = 2) {I : Subgroup G} (hI : Is1911 D V₀ V I)
    {g v u : G} (hv : v ∈ V₀) (hv1 : v ≠ 1)
    (hV₀ : ∀ x ∈ V₀, x = 1 ∨ x = v) (hu : u = g⁻¹ * v * g)
    (hcent : Subgroup.centralizer ({u} : Set G) = conjSubgroup D.M g)
    (hIeq : V₀ ⊔ conjSubgroup V₀ g = I) {k : G} (hk : k ∈ X ⊔ D.T)
    (hIM : I ≤ conjSubgroup D.M (g * k)) :
    ∀ a ∈ I, ∀ b ∈ I, a * (k * b * k⁻¹) = (k * b * k⁻¹) * a := by
  have hkM : k ∈ D.M := c.hyp.le_M hk
  have hIH : I ≤ X ⊔ D.T := hI.1.trans (c.Z193_le_T.trans le_sup_right)
  intro a ha b hb
  have hb'M : k * b * k⁻¹ ∈ D.M :=
    D.M.mul_mem (D.M.mul_mem hkM (c.hyp.le_M (hIH hb))) (D.M.inv_mem hkM)
  have hb'Mg : k * b * k⁻¹ ∈ conjSubgroup D.M g := by
    have h1 : (g * k) * b * (g * k)⁻¹ ∈ D.M := mem_conjSubgroup_iff.1 (hIM hb)
    rw [mem_conjSubgroup_iff]
    rwa [show g * (k * b * k⁻¹) * g⁻¹ = (g * k) * b * (g * k)⁻¹ from by group]
  have hb'C : k * b * k⁻¹ ∈ Subgroup.centralizer ({u} : Set G) := by
    rw [hcent]
    exact hb'Mg
  have hb'v : v * (k * b * k⁻¹) = (k * b * k⁻¹) * v := by
    exact (mul_inv_eq_iff_eq_mul.1
      (c.conj_eq_of_mem_M hv hv1 hV₀ hb'M)).symm
  have hb'u : u * (k * b * k⁻¹) = (k * b * k⁻¹) * u :=
    (Subgroup.mem_centralizer_singleton_iff.1 hb'C).symm
  have hIle : I ≤ Subgroup.centralizer ({k * b * k⁻¹} : Set G) := by
    rw [← hIeq]
    refine sup_le ?_ ?_
    · intro x hx
      rw [Subgroup.mem_centralizer_singleton_iff]
      rcases hV₀ x hx with h | h
      · rw [h]; simp
      · rw [h]; exact hb'v
    · intro x hx
      rw [Subgroup.mem_centralizer_singleton_iff]
      rcases eq_one_or_eq_u_of_mem_conj h2 hv hv1 hu hx with h | h
      · rw [h]; simp
      · rw [h]; exact hb'u
  exact (Subgroup.mem_centralizer_iff.1 (hIle ha) (k * b * k⁻¹) (by simp)).symm

theorem gap1912_of_hyp198 (c : MinCex193 D V₀ V p X) (h2 : Nat.card ↥V₀ = 2)
    {E F : Subgroup G} (hE : Hyp198 D X E F) (hFE : F < E) (hXE : ¬ ⁅X, E⁆ ≤ F)
    (hsq : ∀ g : G, conjSubgroup V g ≤ D.T → ¬ ⁅conjSubgroup V g, E⁆ ≤ F →
      g ^ 2 ∉ D.M) :
    Gap1912 D V₀ V X := by
  intro I hI
  have hIkeep : Is1911 D V₀ V I := hI
  obtain ⟨-, hIcard, hV₀I, hNI, g, hgN, hgM, hg2M⟩ := hI
  obtain ⟨v, hvV, hv1, hV₀⟩ := c.exists_v₀ h2
  let u : G := g⁻¹ * v * g
  have hu : u = g⁻¹ * v * g := rfl
  have hcent : Subgroup.centralizer ({u} : Set G) = conjSubgroup D.M g :=
    centralizer_singleton_eq_conj_M c hvV hv1 hV₀ hu
  have hu1 : u ≠ 1 := by
    intro h
    apply hv1
    have e : v = g * u * g⁻¹ := by rw [hu]; group
    rw [h] at e
    simpa using e
  have huNotV₀ : u ∉ V₀ := by
    intro huV
    rcases hV₀ u huV with h | h
    · exact hu1 h
    · have hgv : g * v * g⁻¹ = v := by
        calc g * v * g⁻¹ = g * u * g⁻¹ := by rw [← h]
          _ = g * (g⁻¹ * v * g) * g⁻¹ := by rw [hu]
          _ = v := by group
      exact hgM (c.mem_M_of_conj_eq hvV hV₀ hgv)
  have hInter : V₀ ⊓ conjSubgroup V₀ g = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxV, hxU⟩ := Subgroup.mem_inf.1 hx
    by_cases hx1 : x = 1
    · exact Subgroup.mem_bot.2 hx1
    · exfalso
      rcases hV₀ x hxV with h | h
      · exact hx1 h
      · rcases eq_one_or_eq_u_of_mem_conj h2 hvV hv1 hu hxU with h' | h'
        · exact hx1 h'
        · exact huNotV₀ (by rw [← h', h]; exact hvV)
  have hconjI : conjSubgroup V₀ g ≤ I := by
    have hIg : conjSubgroup I g = I := conjSubgroup_eq_iff_mem_normalizer.mpr (hNI hgN)
    calc conjSubgroup V₀ g ≤ conjSubgroup I g := E3.conjSubgroup_mono_left g hV₀I
      _ = I := hIg
  have hIeq : V₀ ⊔ conjSubgroup V₀ g = I := by
    refine W19Aux.sup_eq_of_card hV₀I hconjI hInter ?_
    rw [hIcard, h2, E3.card_conjSubgroup, h2]
  have hUT : conjSubgroup V g ≤ D.T :=
    (conjSubgroup_le_wClos_of_is1911 c h2 hgN hg2M hvV hu hcent).trans
      (E3.wClos_le 1 D.T)
  have hUK : conjSubgroup V g ≤ centralizerQuot (X ⊔ D.T) E F :=
    conjSubgroup_le_centralizerQuot_of_sq hE hsq hg2M hUT
  have hU2 : (conjSubgroup V g ⊓ pCoreOf 2 (X ⊔ D.T)).relIndex (conjSubgroup V g) ≤ 2 :=
    step8_relIndex c hE hFE hXE hUT hUK
  intro k hk
  have hkuM : (g * k) * u * (g * k)⁻¹ ∈ D.M :=
    conj_u_mem_M_of_relIndex c h2 hgN hvV hu hU2 hk
  exact comm_of_mem_I_of_is1911 c h2 hIkeep hvV hv1 hV₀ hu hcent hIeq hk
    (le_conj_M_mul_of_is1911 c h2 hvV hv1 hV₀ hu hgN hIeq hk hkuM)

section Certified


theorem gap1912_of_comm_ne_bot (c : MinCex193 D V₀ V p X) (h162 : W3Thm162Gt2 G)
    (h4 : Card196Four D V p X) (hVX : ⁅V, X⁆ ≠ ⊥) : Gap1912 D V₀ V X := by
  obtain ⟨E, F, hE, hFE, hEV, hXE⟩ := c.exists_hyp198 hVX
  obtain ⟨h2, -, hsq⟩ := c.nineteen_ten h162 h4 hE hFE hEV hXE
  exact c.gap1912_of_hyp198 h2 hE hFE hXE hsq

theorem gap1912_holds (c : MinCex193 D V₀ V p X) (h162 : W3Thm162Gt2 G)
    (h4 : Card196Four D V p X) : Gap1912 D V₀ V X :=
  c.gap1912_of_comm_ne_bot h162 h4 c.commutator_ne_bot

end Certified

end MinCex193

end CFSG.LocalAnalysis.WeakClosure81

end
