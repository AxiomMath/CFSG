module

public import CFSG.Timmesfeld.Bridge.RootStructN0Cycle
public import CFSG.Timmesfeld.Bridge.RootStructR2Count

public section

namespace CFSG.Timmesfeld.Bridge

open CFSG.Timmesfeld

variable {G : Type} [Group G] {D : Set G}

@[expose] def UniqueGate (D : Set G) : Prop :=
  ∀ ⦃b x c c' : G⦄, b ∈ D → x ∈ D → ¬ Commute b x → Odd (orderOf (b * x)) → c ∈ D →
    Commute b c → b * c ∈ D → orderOf (x * c) = 4 → c' ∈ D → Commute b c' → b * c' ∈ D →
      orderOf (x * c') = 4 → c' ∈ rootSet D c

@[expose] def IsPeriod (D : Set G) (p : ℤ → G) (k : ℤ) : Prop := ∀ i, p (i + k) ∈ rootSet D (p i)

namespace IsPeriod

variable {p : ℤ → G}

theorem add {k l : ℤ} (hk : IsPeriod D p k) (hl : IsPeriod D p l) : IsPeriod D p (k + l) := by
  intro i
  have h1 := hl (i + k)
  rw [rootSet_eq_of_mem (hk i)] at h1
  rw [← add_assoc]
  exact h1

theorem neg (hD : ∀ i, p i ∈ D) {k : ℤ} (hk : IsPeriod D p k) : IsPeriod D p (-k) := by
  intro i
  have h1 := hk (i + -k)
  rw [neg_add_cancel_right] at h1
  exact mem_rootSet_comm (hD _) h1

theorem sub (hD : ∀ i, p i ∈ D) {k l : ℤ} (hk : IsPeriod D p k) (hl : IsPeriod D p l) :
    IsPeriod D p (k - l) := by
  rw [sub_eq_add_neg]
  exact hk.add (hl.neg hD)

end IsPeriod

namespace TorusPath

variable {g : G} {p : ℤ → G}

theorem mem_rootSet_of_collinear (h : Hyp G D) (hc : RootClosure D) (hs : SpecialClosure D)
    (h3 : ¬ ThreeLines D) (hF : FixUnique D) (hg : InvTorus D g) (hP : TorusPath D g p) {i : ℤ}
    {z : G} (hz : z ∈ D) (hpz : Commute (p i) z) (hpzD : p i * z ∈ D)
    (hzT : z ∉ rootSet D (p i)) (hgz : g * z * g⁻¹ ∈ rootSet D z) :
    z ∈ rootSet D (p (i - 1)) ∨ z ∈ rootSet D (p (i + 1)) := by
  have hclass := h.isClass
  have hsub := hP.turn_sub h hc hs i
  rw [sup_comm] at hsub
  have hsub' : p (i + 1) ∉ rootGroup D (p i) ⊔ rootGroup D (p (i - 1)) := by
    have := hP.turn i
    rwa [sup_comm] at this
  rcases mem_line_or_mem_line_of_not_threeLines h3 (hP.mem i) (hP.mem (i + 1)) (hP.mem (i - 1)) hz
      ⟨hP.comm i, hP.mul_mem i, hP.not_mem i⟩
      ⟨(hP.comm_sub i).symm, hP.mul_mem_sub i, hP.not_mem_sub i⟩ ⟨hpz, hpzD, hzT⟩ hsub
    with h' | h'
  · right
    exact (hF (hP.mem i) (hP.mem (i + 1)) (hP.comm i) (hP.mul_mem i) (hP.not_mem i)
      (hP.mem (i - 1)) (hP.comm_sub i).symm (hP.mul_mem_sub i) hsub hg (hP.fix i)
      (fun u hu => hP.conj_mem_line hclass i hu)
      (fun u hu => hP.conj_mem_line_sub hclass i hu)).2 _ (hP.mem (i + 1))
      (right_mem_line (hP.mem (i + 1))) (hP.not_mem i) (hP.fix (i + 1)) _ hz h' hzT hgz
  · left
    exact (hF (hP.mem i) (hP.mem (i - 1)) (hP.comm_sub i).symm (hP.mul_mem_sub i)
      (hP.not_mem_sub i) (hP.mem (i + 1)) (hP.comm i) (hP.mul_mem i) hsub' hg (hP.fix i)
      (fun u hu => hP.conj_mem_line_sub hclass i hu)
      (fun u hu => hP.conj_mem_line hclass i hu)).2 _ (hP.mem (i - 1))
      (right_mem_line (hP.mem (i - 1))) (hP.not_mem_sub i) (hP.fix (i - 1)) _ hz h' hzT hgz

theorem mem_rootSet_of_special (h : Hyp G D) (hc : RootClosure D) (hs : SpecialClosure D)
    (h3 : ¬ ThreeLines D) (hF : FixUnique D) (hg : InvTorus D g) (hP : TorusPath D g p) {i : ℤ}
    {z : G} (hz : z ∈ D) (h4 : orderOf (p i * z) = 4) (hgz : g * z * g⁻¹ ∈ rootSet D z) :
    z ∈ rootSet D (p (i - 2)) ∨ z ∈ rootSet D (p (i + 2)) := by
  have hclass := h.isClass
  have hD := h.root
  have hpi := hP.mem i
  obtain ⟨hwD, hpw, hzw, -⟩ := sq_mem_of_orderOf_eq_four hD hpi hz h4
  have hpz : ¬ Commute (p i) z :=
    not_commute_of_orderOf_mul_eq_four (hD.mul_self_eq_one hpi) (hD.mul_self_eq_one hz) h4
  set w := (p i * z) ^ 2 with hw
  have hwT : w ∉ rootSet D (p i) := fun h' => hpz ((h'.2 z hz).1 hzw.symm)
  have hpwD : p i * w ∈ D := mul_sq_mem_of_orderOf_eq_four hclass hD hpi hz h4
  have hgw : g * w * g⁻¹ ∈ rootSet D w := by
    have := hs.mul_sq_mem_rootSet hD hpi hz h4 (hP.fix i) hgz
    rwa [show g * p i * g⁻¹ * (g * z * g⁻¹) = g * (p i * z) * g⁻¹ by group, conj_pow] at this
  have h4' : orderOf (z * p i) = 4 := by rwa [orderOf_mul_comm_eq]
  have hzwD : z * w ∈ D := by
    have := mul_sq_mem_of_orderOf_eq_four hclass hD hz hpi h4'
    rwa [← mul_sq_eq_mul_sq_comm (hD.mul_self_eq_one hpi) (hD.mul_self_eq_one hz) h4] at this
  have hzwT : z ∉ rootSet D w := fun h' => hpz ((h'.2 (p i) hpi).2 hpw.symm).symm
  have hziT : z ∉ rootSet D (p i) := fun h' => hpz ((h'.2 (p i) hpi).2 (Commute.refl _)).symm
  have hcolj : ∀ {j : ℤ}, w ∈ rootSet D (p j) →
      Commute (p j) z ∧ p j * z ∈ D ∧ z ∉ rootSet D (p j) := by
    intro j hwj
    have hTw : rootSet D w = rootSet D (p j) := rootSet_eq_of_mem hwj
    have hzjT : z ∉ rootSet D (p j) := by rw [← hTw]; exact hzwT
    obtain ⟨hc1, hc2⟩ := collinear_of_collinear_mem_rootSet h hc hs (hP.mem j) hwj hz hzw hzwD
      hzjT
    exact ⟨hc1, hc2, hzjT⟩
  rcases hP.mem_rootSet_of_collinear h hc hs h3 hF hg hwD hpw hpwD hwT hgw with h' | h'
  · obtain ⟨hc1, hc2, hc3⟩ := hcolj h'
    rcases hP.mem_rootSet_of_collinear h hc hs h3 hF hg hz hc1 hc2 hc3 hgz with h'' | h''
    · left
      rwa [show i - 1 - 1 = i - 2 by ring] at h''
    · rw [sub_add_cancel] at h''
      exact absurd h'' hziT
  · obtain ⟨hc1, hc2, hc3⟩ := hcolj h'
    rcases hP.mem_rootSet_of_collinear h hc hs h3 hF hg hz hc1 hc2 hc3 hgz with h'' | h''
    · rw [add_sub_cancel_right] at h''
      exact absurd h'' hziT
    · right
      rwa [show i + 1 + 1 = i + 2 by ring] at h''

theorem mem_rootSet_of_oneOpposite (h : Hyp G D) (hc : RootClosure D) (hs : SpecialClosure D)
    (h3 : ¬ ThreeLines D) (hF : FixUnique D) (hU : UniqueGate D) (hg : InvTorus D g)
    (hP : TorusPath D g p) {i : ℤ} {z : G} (hz : z ∈ D) (hpz : ¬ Commute (p i) z)
    (hoddpz : Odd (orderOf (p i * z))) (h1 : OneOpposite D (p i) z)
    (hgz : g * z * g⁻¹ ∈ rootSet D z) :
    z ∈ rootSet D (p (i - 3)) ∨ z ∈ rootSet D (p (i + 3)) := by
  have hclass := h.isClass
  have hD := h.root
  have hpi := hP.mem i
  obtain ⟨c, hcD, hpc, hpcD, h4⟩ := h1
  have h4c : orderOf (c * z) = 4 := by rwa [orderOf_mul_comm_eq]
  have hcT : c ∉ rootSet D (p i) := fun h' => by
    have := (orderOf_mul_eq_four_iff_of_mem_rootSet hD hpi h' hz).1 h4c
    rw [this] at hoddpz
    exact absurd hoddpz (by decide)
  have hgcD : g * c * g⁻¹ ∈ D := conj_mem_of_isClass hclass g hcD
  have hgcT : g * c * g⁻¹ ∉ rootSet D (p i) := by
    rw [← rootSet_eq_of_mem (hP.fix i), rootSet_conj hclass]
    rintro ⟨y, hy, hye⟩
    have : y = c := by
      have := congrArg (fun w => g⁻¹ * w * g) hye
      simpa [mul_assoc] using this
    exact hcT (this ▸ hy)
  obtain ⟨hgc1, hgc2⟩ := collinear_of_collinear_mem_rootSet h hc hs hpi (hP.fix i) hgcD
    ((Commute.conj_iff g).2 hpc).symm (by
      have := conj_mem_of_isClass hclass g hpcD
      rwa [show g * (p i * c) * g⁻¹ = g * c * g⁻¹ * (g * p i * g⁻¹) by
        rw [show p i * c = c * p i from hpc.eq]; group] at this) hgcT
  have h4gc : orderOf (z * (g * c * g⁻¹)) = 4 := by
    have h' : orderOf (g * z * g⁻¹ * (g * c * g⁻¹)) = 4 := by
      rw [show g * z * g⁻¹ * (g * c * g⁻¹) = g * (z * c) * g⁻¹ by group, orderOf_conj_eq]
      exact h4
    exact (orderOf_mul_eq_four_iff_of_mem_rootSet hD hz hgz hgcD).1 h'
  have hgc : g * c * g⁻¹ ∈ rootSet D c :=
    hU hpi hz hpz hoddpz hcD hpc hpcD h4 hgcD hgc1 hgc2 h4gc
  have hzi1 : ∀ {j : ℤ}, z ∈ rootSet D (p j) → Commute (p i) (p j) → False := fun hzj hij =>
    hpz ((hzj.2 (p i) hpi).2 hij.symm).symm
  rcases hP.mem_rootSet_of_collinear h hc hs h3 hF hg hcD hpc hpcD hcT hgc with h' | h'
  · have h4' : orderOf (p (i - 1) * z) = 4 :=
      (orderOf_mul_eq_four_iff_of_mem_rootSet hD (hP.mem _) h' hz).1 h4c
    rcases hP.mem_rootSet_of_special h hc hs h3 hF hg hz h4' hgz with h'' | h''
    · left
      rwa [show i - 1 - 2 = i - 3 by ring] at h''
    · rw [show i - 1 + 2 = i + 1 by ring] at h''
      exact (hzi1 h'' (hP.comm i)).elim
  · have h4' : orderOf (p (i + 1) * z) = 4 :=
      (orderOf_mul_eq_four_iff_of_mem_rootSet hD (hP.mem _) h' hz).1 h4c
    rcases hP.mem_rootSet_of_special h hc hs h3 hF hg hz h4' hgz with h'' | h''
    · rw [show i + 1 - 2 = i - 1 by ring] at h''
      exact (hzi1 h'' (hP.comm_sub i).symm).elim
    · right
      rwa [show i + 1 + 2 = i + 3 by ring] at h''

theorem isPeriod_of_mem_rootSet (h : Hyp G D) (hc : RootClosure D) (hs : SpecialClosure D)
    (h3 : ¬ ThreeLines D) (hF : FixUnique D) (hg : InvTorus D g) (hP : TorusPath D g p)
    {a b : ℤ} (hab : p b ∈ rootSet D (p a)) : IsPeriod D p (b - a) := by
  have hT : rootSet D (p b) = rootSet D (p a) := rootSet_eq_of_mem hab
  have hT1 : p (b + 1) ∉ rootSet D (p a) := by
    rw [← hT]
    exact hP.not_mem b
  obtain ⟨hc1, hc2⟩ := collinear_of_collinear_mem_rootSet h hc hs (hP.mem a) hab (hP.mem (b + 1))
    (hP.comm b).symm (by rw [← (hP.comm b).eq]; exact hP.mul_mem b) hT1
  rcases hP.mem_rootSet_of_collinear h hc hs h3 hF hg (hP.mem (b + 1)) hc1 hc2 hT1
      (hP.fix (b + 1)) with h' | h'
  · exfalso
    have hR := hP.reverse h hc hs (a + b)
    have h0' : p (a + b - (a - 1)) ∈ rootSet D (p (a - 1)) := by
      rw [show a + b - (a - 1) = b + 1 by ring]
      exact h'
    have h1' : p (a + b - (a - 1 + 1)) ∈ rootSet D (p (a - 1 + 1)) := by
      rw [show a - 1 + 1 = a by ring, show a + b - a = b by ring]
      exact hab
    have hrig := rootSet_of_rootSet h hc hs h3 hF hg hP hR h0' h1'
    rcases Int.even_or_odd (a + b) with ⟨m, hm⟩ | ⟨m, hm⟩
    · have := hrig (m + 1)
      rw [show a + b - (m + 1) = m - 1 by omega] at this
      apply hP.turn m
      exact Subgroup.mem_sup_left (rootSet_subset_rootGroup D _
        (mem_rootSet_comm (hP.mem _) this))
    · have := hrig (m + 1)
      rw [show a + b - (m + 1) = m by omega] at this
      exact hP.not_mem m (mem_rootSet_comm (hP.mem _) this)
  · intro i
    have h0' : p (a + (b - a)) ∈ rootSet D (p a) := by
      rw [show a + (b - a) = b by ring]
      exact hab
    have h1' : p (a + 1 + (b - a)) ∈ rootSet D (p (a + 1)) := by
      rw [show a + 1 + (b - a) = b + 1 by ring]
      exact h'
    exact rootSet_of_rootSet h hc hs h3 hF hg hP (hP.shift (b - a)) h0' h1' i

theorem false_of_isPeriod_le_six (h : Hyp G D) (hc : RootClosure D) (hs : SpecialClosure D)
    (hconn : Moufang.ExcCollConnected D) (hAll : AllLinesTI D) (hbad : ThinAllBad D)
    (h3 : ¬ ThreeLines D) (hP : TorusPath D g p) (h03 : ¬ Commute (p 0) (p 3))
    (hodd03 : Odd (orderOf (p 0 * p 3))) {k : ℤ} (hk : IsPeriod D p k) (hk0 : 0 < k)
    (hk6 : k ≤ 6) : False := by
  have hD := h.root
  interval_cases k
  · exact hP.not_mem 0 (hk 0)
  · have h2 : p 2 ∈ rootSet D (p 0) := by simpa using hk 0
    have ht : p 2 ∉ rootGroup D (p 0) ⊔ rootGroup D (p 1) := by simpa using hP.turn 1
    exact ht (Subgroup.mem_sup_left (rootSet_subset_rootGroup D _ h2))
  · have h3' : p 3 ∈ rootSet D (p 0) := by simpa using hk 0
    exact h03 ((h3'.2 (p 0) (hP.mem 0)).2 (Commute.refl _)).symm
  · have h4' : p 4 ∈ rootSet D (p 0) := by simpa using hk 0
    have h34 : Commute (p 3) (p 4) := by simpa using hP.comm 3
    exact h03 ((h4'.2 (p 3) (hP.mem 3)).1 h34.symm)
  · have h5' : p 5 ∈ rootSet D (p 0) := by simpa using hk 0
    have h45 : Commute (p 4) (p 5) := by simpa using hP.comm 4
    have h45D : p 4 * p 5 ∈ D := by simpa using hP.mul_mem 4
    have h5T : p 5 ∉ rootSet D (p 4) := by simpa using hP.not_mem 4
    have h4T : p 4 ∉ rootSet D (p 0) := by
      rw [← rootSet_eq_of_mem h5']
      exact fun h' => h5T (mem_rootSet_comm (hP.mem 5) h')
    obtain ⟨hc1, hc2⟩ := collinear_of_collinear_mem_rootSet h hc hs (hP.mem 0) h5' (hP.mem 4) h45
      h45D h4T
    have h34 : Commute (p 3) (p 4) := by simpa using hP.comm 3
    have hodd30 : Odd (orderOf (p 3 * p 0)) := by rwa [orderOf_mul_comm_eq]
    exact not_commute_of_collinear hD (hP.mem 3) (hP.mem 4) (fun h' => h03 h'.symm) hodd30 hc1
      hc2 h34
  ·
    have h12 : Commute (p 1) (p 2) := by simpa using hP.comm 1
    have h23 : Commute (p 2) (p 3) := by simpa using hP.comm 2
    have h4a : orderOf (p 3 * p 1) = 4 := by
      rw [orderOf_mul_comm_eq]
      exact orderOf_mul_eq_four_of_path h hc hs hconn hAll (hP.mem 1) (hP.mem 2) (hP.mem 3) h12
        (by simpa using hP.mul_mem 1) (by simpa using hP.not_mem 1) h23
        (by simpa using hP.mul_mem 2) (by simpa using hP.turn 2)
    have h4b : orderOf (p 3 * p 5) = 4 :=
      orderOf_mul_eq_four_of_path h hc hs hconn hAll (hP.mem 3) (hP.mem 4) (hP.mem 5)
        (by simpa using hP.comm 3) (by simpa using hP.mul_mem 3) (by simpa using hP.not_mem 3)
        (by simpa using hP.comm 4) (by simpa using hP.mul_mem 4) (by simpa using hP.turn 4)
    have h5m : p 5 ∈ rootSet D (p (-1)) := by simpa using hk (-1)
    have h4c : orderOf (p 3 * p (-1)) = 4 := by
      rw [orderOf_mul_comm_eq]
      refine (orderOf_mul_eq_four_iff_of_mem_rootSet hD (hP.mem (-1)) h5m (hP.mem 3)).1 ?_
      rwa [orderOf_mul_comm_eq]
    have col₁ : Commute (p 0) (p 1) ∧ p 0 * p 1 ∈ D ∧ p 1 ∉ rootSet D (p 0) := by
      simpa using ⟨hP.comm 0, hP.mul_mem 0, hP.not_mem 0⟩
    have col₂ : Commute (p 0) (p (-1)) ∧ p 0 * p (-1) ∈ D ∧ p (-1) ∉ rootSet D (p 0) := by
      simpa using ⟨(hP.comm_sub 0).symm, hP.mul_mem_sub 0, hP.not_mem_sub 0⟩
    have h21 : p (-1) ∉ rootGroup D (p 0) ⊔ rootGroup D (p 1) := by
      have := hP.turn_sub h hc hs 0
      rw [sup_comm] at this
      simpa using this
    refine hbad (p 0) (hP.mem 0) (p 3) (hP.mem 3) h03 hodd03
      ⟨p 1, hP.mem 1, col₁.1, col₁.2.1, h4a⟩ fun a ha hpa hpaD haT => ?_
    rcases mem_line_or_mem_line_of_not_threeLines h3 (hP.mem 0) (hP.mem 1) (hP.mem (-1)) ha col₁
        col₂ ⟨hpa, hpaD, haT⟩ h21 with h' | h'
    · refine ⟨p 1, hP.mem 1, ?_, h4a⟩
      rw [sup_rootGroup_eq_of_mem h hc hs (hP.mem 0) (hP.mem 1) col₁.1 col₁.2.1 col₁.2.2
        (left_mem_line (hP.mem 0)) h' (hD.ne_one (hP.mem 0)) (hD.ne_one ha) haT]
      exact right_mem_line (hP.mem 1)
    · refine ⟨p (-1), hP.mem (-1), ?_, h4c⟩
      rw [sup_rootGroup_eq_of_mem h hc hs (hP.mem 0) (hP.mem (-1)) col₂.1 col₂.2.1 col₂.2.2
        (left_mem_line (hP.mem 0)) h' (hD.ne_one (hP.mem 0)) (hD.ne_one ha) haT]
      exact right_mem_line (hP.mem (-1))

end TorusPath

end CFSG.Timmesfeld.Bridge
