module

public import Certificates.Data.Kernel.PermCent.U43P1

public section

namespace CFSG.ComponentClassification.HarrisLit.P1.U43.Cover

@[expose] def tuLs (l : List (ℕ × Bool)) : Array (Array ℕ) := (l.map fun x => tuL x.1 x.2).toArray

@[expose] def sylM1 : List (ℕ × Bool) := [(681419464198167, false), (789656130700282, false),
  (648847729602246, false), (803491913225569, false)]

@[expose] def sylF : List (ℕ × Bool) := [(929688581196673, true), (800492117728047, true),
  (31819884297376, false), (816059375422670, false)]

@[expose] def sylI : List (ℕ × Bool) := [(1361372700198827, false), (1388474143284150, true),
  (1227083113103251, false)]

@[expose] def cgIn : List (ℕ × Bool) := [(461784471641496, false), (951056191197011, false)]

@[expose] def gsIn : List (ℕ × Bool) := [(973358761385775, false), (990333992335712, false)]

@[expose] def gsFb : List (ℕ × Bool) := [(1077849993127753, false), (1186955063061972, false)]

@[expose] def cgM1a : List (ℕ × Bool) := [(199356355501045, false), (1502333418824710, false)]

@[expose] def lM1a : List ℕ := [717036406373775, 1262543510265003]

@[expose] def cgIa : List (ℕ × Bool) := [(1784977595901434, false), (272148944697276, false)]

@[expose] def lIa : List ℕ := [704289276109470, 681238911387358]

@[expose] def a6Gens : List (List ℕ) := [[1, 2, 0, 3, 4, 5], [0, 2, 3, 4, 5, 1]]

@[expose] def wM1a : List (ℕ × Bool) := [(617683856814300, false), (272258491589282, false),
  (1623684934555675, true), (1819279150078127, true), (1321803437050047, true),
  (1265182618290281, true)]

@[expose] def wIa : List (ℕ × Bool) := [(617683856814300, false), (107428027916842, false),
  (385898992524779, true), (1501335062711990, true)]

@[expose] def tM1a : List (List (ℕ × Bool)) := [
  [(185232020972379, false), (1811033877073441, false), (230215241468277, false)],
  [(104495209900513, false), (789110039638577, false), (1130818860715795, false),
    (1684910116012663, false)],
  [(644130179782983, true), (1532276400050708, true), (1691480311940353, false),
    (550396040361893, false)],
  [(428450796936450, true), (185232020972379, false), (280264851896110, true)],
  [(1321803437050047, true), (175829299869456, true), (1572505419994655, false),
    (1244405473180650, false)],
  [(1265182618290281, true), (64123646135490, true), (1244405473180650, false)]]

@[expose] def tIa : List (List (ℕ × Bool)) := [
  [(1784977595901434, false), (148095089382772, false)],
  [(1784977595901434, false), (291659500212463, false), (368699176209278, false)],
  [(1784977595901434, false), (949816993220508, true), (1263621821529213, false)],
  [(1784977595901434, false), (891133888750908, true), (148095089382772, false)]]

@[expose] def tM1aL (k : ℕ) : Array (Array ℕ) := tuLs (tM1a.getD k [])

@[expose] def tIaL (k : ℕ) : Array (Array ℕ) := tuLs (tIa.getD k [])

@[expose] def tM1aL0 : Array (Array ℕ) := tM1aL 0

@[expose] def tM1aL1 : Array (Array ℕ) := tM1aL 1

@[expose] def tM1aL2 : Array (Array ℕ) := tM1aL 2

@[expose] def tM1aL3 : Array (Array ℕ) := tM1aL 3

@[expose] def tM1aL4 : Array (Array ℕ) := tM1aL 4

@[expose] def tM1aL5 : Array (Array ℕ) := tM1aL 5

@[expose] def tIaL0 : Array (Array ℕ) := tIaL 0

@[expose] def tIaL1 : Array (Array ℕ) := tIaL 1

@[expose] def tIaL2 : Array (Array ℕ) := tIaL 2

@[expose] def tIaL3 : Array (Array ℕ) := tIaL 3

@[expose] def sylM1L : Array (Array ℕ) := tuLs sylM1

@[expose] def sylFL : Array (Array ℕ) := tuLs sylF

@[expose] def sylIL : Array (Array ℕ) := tuLs sylI

@[expose] def cgInL : Array (Array ℕ) := tuLs cgIn

@[expose] def gsInL : Array (Array ℕ) := tuLs gsIn

@[expose] def gsFbL : Array (Array ℕ) := tuLs gsFb

@[expose] def cgM1aL : Array (Array ℕ) := tuLs cgM1a

@[expose] def lM1aL : Array (Array ℕ) := tuLs (lM1a.map (·, false))

@[expose] def cgIaL : Array (Array ℕ) := tuLs cgIa

@[expose] def lIaL : Array (Array ℕ) := tuLs (lIa.map (·, false))

@[expose] def dgM1aL : Array (Array ℕ) := (lM1a.zipWith diagL a6Gens).toArray

@[expose] def dgIaL : Array (Array ℕ) := (lIa.zipWith diagL a6Gens).toArray

@[expose] def a6L : Array (Array ℕ) := (a6Gens.map List.toArray).toArray

@[expose] def baseT : List ℕ := [0, 1, 9, 2, 3, 10, 100]

@[expose] def base6 : List ℕ := [0, 1, 2, 3]

end CFSG.ComponentClassification.HarrisLit.P1.U43.Cover
